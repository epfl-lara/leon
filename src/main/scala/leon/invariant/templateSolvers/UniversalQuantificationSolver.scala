package leon
package invariant.templateSolvers

import z3.scala._
import purescala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import evaluators._
import java.io._
import solvers._
import solvers.combinators._
import solvers.smtlib._
import solvers.z3._
import scala.util.control.Breaks._
import purescala.ScalaPrinter
import scala.collection.mutable.{ Map => MutableMap }
import scala.reflect.runtime.universe
import invariant.engine._
import invariant.factories._
import invariant.util._
import invariant.util.ExpressionTransformer._
import invariant.structure._
import invariant.structure.FunctionUtils._
import Stats._
import leon.evaluators._
import EvaluationResults._

import Util._
import PredicateUtil._
import SolverUtil._

class UniversalQuantificationSolver(ctx: InferenceContext, program: Program,
                                    funs: Seq[FunDef], ctrTracker: ConstraintTracker,
                                    minimizer: Option[(Expr, Model) => Model]) {

  import NLTemplateSolver._

  //flags controlling debugging
  val debugUnflattening = false
  val debugIncrementalVC = false
  val trackCompressedVCCTime = false

  val printCounterExample = false
  val dumpInstantiatedVC = false

  val reporter = ctx.reporter
  val timeout = ctx.vcTimeout
  val leonctx = ctx.leonContext

  //flag controlling behavior
  val disableCegis = true
  private val useIncrementalSolvingForVCs = true
  private val usePortfolio = false // portfolio has a bug in incremental solving

  val defaultEval = new DefaultEvaluator(leonctx, program) // an evaluator for extracting models
  val existSolver = new ExistentialQuantificationSolver(ctx, program, ctrTracker, defaultEval)

  val solverFactory =
    if (usePortfolio) {
      if (useIncrementalSolvingForVCs)
        throw new IllegalArgumentException("Cannot perform incremental solving with portfolio solvers!")
      new PortfolioSolverFactory(leonctx.toSctx, Seq(
        SolverFactory.getFromName(leonctx, program)("smt-cvc4-u"),
        SolverFactory.getFromName(leonctx, program)("smt-z3-u")))
    } else
      SolverFactory.uninterpreted(leonctx, program)

  def splitVC(fd: FunDef) = {
    val (paramPart, rest, modCons) =
      time { ctrTracker.getVC(fd).toUnflatExpr } {
        t => Stats.updateCounterTime(t, "UnflatTime", "VC-refinement")
      }
    if (ctx.usereals) {
      (IntLiteralToReal(paramPart), IntLiteralToReal(rest), modCons)
    } else (paramPart, rest, modCons)
  }

  case class FunData(modelCons: (Model, DefaultEvaluator) => FlatModel, paramParts: Expr, simpleParts: Expr)
  val funInfos = funs.map { fd =>
    val (paramPart, rest, modelCons) = splitVC(fd)
    if (hasReals(rest) && hasInts(rest))
      throw new IllegalStateException("Non-param Part has both integers and reals: " + rest)
    if (debugIncrementalVC) {
      assert(getTemplateVars(rest).isEmpty)
      println("For function: " + fd.id)
      println("Param part: " + paramPart)
    }
    (fd -> FunData(modelCons, paramPart, rest))
  }.toMap

  var funSolvers = initializeSolvers
  def initializeSolvers =
    if (!ctx.abort) { // this is required to ensure that solvers are not created after interrupts
      funInfos.map {
        case (fd, FunData(_, _, rest)) =>
          val vcSolver = solverFactory.getNewSolver()
          vcSolver.assertCnstr(rest)
          (fd -> vcSolver)
      }.toMap
    } else Map[FunDef, Solver with TimeoutSolver]()

  def free = {
    if (useIncrementalSolvingForVCs)
      funSolvers.foreach(entry => entry._2.free)
  }

  /**
   * State for minimization
   */
  class MinimizationInfo {
    var minStarted = false
    var lastCorrectModel: Option[Model] = None
    var minStartTime: Long = 0 // for stats

    def started = minStarted
    def reset() = {
      minStarted = false
      lastCorrectModel = None
    }
    def updateProgress(model: Model) {
      lastCorrectModel = Some(model)
      if (!minStarted) {
        minStarted = true
        minStartTime = System.currentTimeMillis()
      }
    }
    def complete {
      reset()
      /*val mintime = (System.currentTimeMillis() - minStartTime)
      Stats.updateCounterTime(mintime, "minimization-time", "procs")
    	Stats.updateCumTime(mintime, "Total-Min-Time")*/
    }
    def getLastCorrectModel = lastCorrectModel
  }

  /**
   * State for recording diffcult paths
   */
  class DifficultPaths {
    var paths = MutableMap[FunDef, Seq[Expr]]()

    def addPath(fd: FunDef, cePath: Expr): Unit = {
      if (paths.contains(fd)) {
        paths.update(fd, cePath +: paths(fd))
      } else {
        paths += (fd -> Seq(cePath))
      }
    }
    def get(fd: FunDef) = paths.get(fd)
    def hasPath(fd: FunDef) = paths.contains(fd)
    def pathsToExpr(fd: FunDef) = Not(createOr(paths(fd)))
    def size = paths.values.map(_.size).sum
  }

  abstract class RefineRes
  case class UnsolvableVC() extends RefineRes
  case class NoSolution() extends RefineRes
  case class CorrectSolution() extends RefineRes
  case class NewSolution(tempModel: Model) extends RefineRes

  class ModelRefiner(tempModel: Model) {
    val tempVarMap: Map[Expr, Expr] = tempModel.map { case (k, v) => (k.toVariable -> v) }.toMap
    val seenPaths = new DifficultPaths()
    private var callsInPaths = Set[Call]()

    def callsEncountered = callsInPaths

    def nextCandidate(conflicts: Seq[FunDef]): RefineRes = {
      var newConflicts = Seq[FunDef]()
      var blockedPaths = false
      val newctrsOpt = conflicts.foldLeft(Some(Seq()): Option[Seq[Expr]]) {
        case (None, _)        => None
        case _ if (ctx.abort) => None
        case (Some(acc), fd) =>
          val disabledPaths =
            if (seenPaths.hasPath(fd)) {
              blockedPaths = true
              seenPaths.pathsToExpr(fd)
            } else tru
          checkVCSAT(fd, tempModel, disabledPaths) match {
            case (None, _)        => None // VC cannot be decided
            case (Some(false), _) => Some(acc) // VC is unsat
            case (Some(true), univModel) => // VC is sat
              newConflicts :+= fd
              if (verbose) reporter.info("Function: " + fd.id + "--Found candidate invariant is not a real invariant! ")
              if (printCounterExample) {
                reporter.info("Model: " + univModel)
              }
              // generate constraints for making preventing the model
              val (existCtr, linearpath, calls) = existSolver.generateCtrsForUNSAT(fd, univModel, tempModel)
              if (existCtr == tru) throw new IllegalStateException("Cannot find a counter-example path!!")
              callsInPaths ++= calls
              //instantiate the disjunct
              val cePath = simplifyArithmetic(TemplateInstantiator.instantiate(
                createAnd(linearpath.map(_.template)), tempVarMap))
              //some sanity checks
              if (variablesOf(cePath).exists(TemplateIdFactory.IsTemplateIdentifier _))
                throw new IllegalStateException("Found template identifier in counter-example disjunct: " + cePath)
              seenPaths.addPath(fd, cePath)
              Some(acc :+ existCtr)
          }
      }
      newctrsOpt match {
        case None => // give up, the VC cannot be decided
          UnsolvableVC()
        case Some(newctrs) if (newctrs.isEmpty) =>
          if (!blockedPaths) { //yes, hurray,found an inductive invariant
            CorrectSolution()
          } else {
            //give up, only hard paths remaining
            reporter.info("- Exhausted all easy paths !!")
            reporter.info("- Number of remaining hard paths: " + seenPaths.size)
            NoSolution() //TODO: what to unroll here ?
          }
        case Some(newctrs) =>
          existSolver.solveConstraints(newctrs, tempModel) match {
            case (None, _) =>
              //here we have timed out while solving the non-linear constraints
              if (verbose)
                reporter.info("NLsolver timed-out on the disjunct... blocking this disjunct...")
              Stats.updateCumStats(1, "retries")
              nextCandidate(newConflicts)
            case (Some(false), _) => // template not solvable, need more unrollings here
              NoSolution()
            case (Some(true), nextModel) =>
              NewSolution(nextModel)
          }
      }
    }
    def nextCandidate: RefineRes = nextCandidate(funs)
  }

  /**
   * @param foundModel a call-back that will be invoked every time a new model is found
   */
  def solveUNSAT(initModel: Model, foundModel: Model => Unit): (Option[Model], Option[Set[Call]]) = {
    val minInfo = new MinimizationInfo()
    var sat: Option[Boolean] = Some(true)
    var tempModel = initModel
    var callsInPaths = Set[Call]()
    var minimized = false
    while (sat == Some(true) && !ctx.abort) {
      Stats.updateCounter(1, "disjuncts")
      if (verbose) {
        reporter.info("Candidate invariants")
        TemplateInstantiator.getAllInvariants(tempModel, ctrTracker.getFuncs).foreach{
          case(f, inv) => reporter.info(f.id + "-->" + PrettyPrinter(inv))
        }
      }
      val modRefiner = new ModelRefiner(tempModel)
      sat = modRefiner.nextCandidate match {
        case CorrectSolution() if (minimizer.isDefined && !minimized) =>
          minInfo.updateProgress(tempModel)
          val minModel = minimizer.get(existSolver.getSolvedCtrs, tempModel)
          minimized = true
          if (minModel.toMap == tempModel.toMap) {
            minInfo.complete
            Some(false)
          } else {
            tempModel = minModel
            Some(true)
          }
        case CorrectSolution() => // minimization has completed or is not applicable
          minInfo.complete
          Some(false)
        case NewSolution(newModel) =>
          foundModel(newModel)
          minimized = false
          tempModel = newModel
          Some(true)
        case NoSolution() => // here template is unsolvable or only hard paths remain
          None
        case UnsolvableVC() if minInfo.started =>
          tempModel = minInfo.getLastCorrectModel.get
          Some(false)
        case UnsolvableVC() if !ctx.abort =>
          if (verbose) {
            reporter.info("VC solving failed!...retrying with a bigger model...")
          }
          existSolver.solveConstraints(retryStrategy(tempModel), tempModel) match {
            case (Some(true), newModel) =>
              foundModel(newModel)
              tempModel = newModel
              funSolvers = initializeSolvers // reinitialize all VC solvers as they all timed out
              Some(true)
            case _ => // give up, no other bigger invariant exist or existential solving timed out!
              None
          }
        case _ => None
      }
      callsInPaths ++= modRefiner.callsEncountered
    }
    sat match {
      case _ if ctx.abort => (None, None)
      case None           => (None, Some(callsInPaths)) //cannot solve template, more unrollings
      case _              => (Some(tempModel), None) // template solved
    }
  }

  /**
   * Strategy: try to find a value for templates that is bigger than the current value
   */
  import RealValuedExprEvaluator._
  val rtwo = FractionalLiteral(2, 1)
  def retryStrategy(tempModel: Model): Seq[Expr] = {
    tempModel.map {
      case (id, z @ FractionalLiteral(n, _)) if n == 0 => GreaterThan(id.toVariable, z)
      case (id, fl: FractionalLiteral)                 => GreaterThan(id.toVariable, evaluate(RealTimes(rtwo, fl)))
    }.toSeq
  }

  protected def instantiateTemplate(e: Expr, tempVarMap: Map[Expr, Expr]): Expr = {
    if (ctx.usereals) replace(tempVarMap, e)
    else
      simplifyArithmetic(TemplateInstantiator.instantiate(e, tempVarMap))
  }

  /**
   * Checks if the VC of fd is unsat
   */
  def checkVCSAT(fd: FunDef, tempModel: Model, disabledPaths: Expr): (Option[Boolean], LazyModel) = {
    val tempIdMap = tempModel.toMap
    val tempVarMap: Map[Expr, Expr] = tempIdMap.map { case (k, v) => k.toVariable -> v }.toMap
    val funData = funInfos(fd)
    val (solver, instExpr, modelCons) =
      if (useIncrementalSolvingForVCs) {
        val instParamPart = instantiateTemplate(funData.paramParts, tempVarMap)
        (funSolvers(fd), And(instParamPart, disabledPaths), funData.modelCons)
      } else {
        val FunData(modCons, paramPart, rest) = funData
        val instPart = instantiateTemplate(paramPart, tempVarMap)
        (solverFactory.getNewSolver(), createAnd(Seq(rest, instPart, disabledPaths)), modCons)
      }
    //For debugging
    if (dumpInstantiatedVC) {
      val fullExpr = if (useIncrementalSolvingForVCs) And(funData.simpleParts, instExpr) else instExpr
      ExpressionTransformer.PrintWithIndentation("vcInst", fullExpr)
    }
    // sanity check
    if (hasMixedIntReals(instExpr))
      throw new IllegalStateException("Instantiated VC of " + fd.id + " contains mixed integer/reals: " + instExpr)
    //reporter.info("checking VC inst ...")
    solver.setTimeout(timeout * 1000)
    val (res, packedModel) =
      time {
        if (useIncrementalSolvingForVCs) {
          solver.push
          solver.assertCnstr(instExpr)
          val solRes = solver.check match {
            case _ if ctx.abort =>
              (None, Model.empty)
            case r @ Some(true) =>
              (r, solver.getModel)
            case r => (r, Model.empty)
          }
          if (solRes._1.isDefined) // invoking pop() otherwise will throw an exception
            solver.pop()
          solRes
        } else
          SimpleSolverAPI(SolverFactory(solver.name, () => solver)).solveSAT(instExpr)
      } { vccTime =>
        if (verbose) reporter.info("checked VC inst... in " + vccTime / 1000.0 + "s")
        updateCounterTime(vccTime, "VC-check-time", "disjuncts")
        updateCumTime(vccTime, "TotalVCCTime")
      }
    if (debugUnflattening) {
      /*ctrTracker.getVC(fd).checkUnflattening(tempVarMap,
        SimpleSolverAPI(SolverFactory(() => solverFactory.getNewSolver())),
        defaultEval)*/
      verifyModel(funData.simpleParts, packedModel, SimpleSolverAPI(solverFactory))
      //val unflatPath = ctrTracker.getVC(fd).pickSatFromUnflatFormula(funData.simpleParts, packedModel, defaultEval)
    }
    //for statistics
    if (trackCompressedVCCTime) {
      val compressedVC =
        unflatten(simplifyArithmetic(instantiateTemplate(ctrTracker.getVC(fd).eliminateBlockers, tempVarMap)))
      Stats.updateCounterStats(atomNum(compressedVC), "Compressed-VC-size", "disjuncts")
      time {
        SimpleSolverAPI(solverFactory).solveSAT(compressedVC)
      } { compTime =>
        Stats.updateCumTime(compTime, "TotalCompressVCCTime")
        reporter.info("checked compressed VC... in " + compTime / 1000.0 + "s")
      }
    }
    (res, modelCons(packedModel, defaultEval))
  }

  // cegis code, now not used
  //val (cres, cctr, cmodel) = solveWithCegis(tempIds.toSet, createOr(newConfDisjuncts), inputCtr, Some(model))
  //  def solveWithCegis(tempIds: Set[Identifier], expr: Expr, precond: Expr, initModel: Option[Model]): (Option[Boolean], Expr, Model) = {
  //      val cegisSolver = new CegisCore(ctx, program, timeout.toInt, NLTemplateSolver.this)
  //      val (res, ctr, model) = cegisSolver.solve(tempIds, expr, precond, solveAsInt = false, initModel)
  //      if (res.isEmpty)
  //        reporter.info("cegis timed-out on the disjunct...")
  //      (res, ctr, model)
  //    }

}
