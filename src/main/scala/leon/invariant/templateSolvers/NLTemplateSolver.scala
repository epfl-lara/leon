package leon
package invariant.templateSolvers

import z3.scala._
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

import Util._
import PredicateUtil._
import SolverUtil._

class NLTemplateSolver(ctx: InferenceContext, program: Program,
                       rootFun: FunDef, ctrTracker: ConstraintTracker,
                       minimizer: Option[(Expr, Model) => Model])
    extends TemplateSolver(ctx, rootFun, ctrTracker) {

  //flags controlling debugging
  val debugUnflattening = false
  val debugIncrementalVC = false
  val debugElimination = false
  val debugChooseDisjunct = false
  val debugTheoryReduction = false
  val debugAxioms = false
  val verifyInvariant = false
  val debugReducedFormula = false
  val trackCompressedVCCTime = false

  //print flags
  val verbose = true
  val printCounterExample = false
  val printPathToConsole = false
  val dumpPathAsSMTLIB = false
  val printCallConstriants = false
  val dumpInstantiatedVC = false

  private val timeout = ctx.vcTimeout
  private val leonctx = ctx.leonContext

  //flag controlling behavior
  private val farkasSolver = new FarkasLemmaSolver(ctx, program)
  private val startFromEarlierModel = true
  private val disableCegis = true
  private val useIncrementalSolvingForVCs = true
  private val usePortfolio = false // portfolio has a bug in incremental solving

  // an evaluator for extracting models
  val defaultEval = new DefaultEvaluator(leonctx, program)
  // an evaluator for quicky checking the result of linear predicates
  val linearEval = new LinearRelationEvaluator(ctx)
  // solver factory
  val solverFactory =
    if (usePortfolio) {
      if (useIncrementalSolvingForVCs)
        throw new IllegalArgumentException("Cannot perform incremental solving with portfolio solvers!")
      SolverFactory(() => new PortfolioSolver(leonctx, Seq(new SMTLIBCVC4Solver(leonctx, program),
        new SMTLIBZ3Solver(leonctx, program))) with TimeoutSolver)
    } else
      SolverFactory.uninterpreted(leonctx, program)

  // state for tracking the last model
  private var lastFoundModel: Option[Model] = None

  /**
   * This function computes invariants belonging to the given templates incrementally.
   * The result is a mapping from function definitions to the corresponding invariants.
   */
  override def solve(tempIds: Set[Identifier], funs: Seq[FunDef]): (Option[Model], Option[Set[Call]]) = {
    val initModel =
      if (this.startFromEarlierModel && lastFoundModel.isDefined) {
        val candModel = lastFoundModel.get
        new Model(tempIds.map(id =>
          (id -> candModel.getOrElse(id, simplestValue(id.getType)))).toMap)
      } else {
        new Model(tempIds.map((id) =>
          (id -> simplestValue(id.getType))).toMap)
      }
    val cgSolver = new CGSolver(funs)
    val (resModel, seenCalls, lastModel) = cgSolver.solveUNSAT(initModel)
    lastFoundModel = Some(lastModel)
    cgSolver.free
    (resModel, seenCalls)
  }

  /**
   * This solver does not use any theories other than UF/ADT. It assumes that other theories are axiomatized in the VC.
   * This method can overloaded by the subclasses.
   */
  protected def axiomsForTheory(formula: Formula, calls: Set[Call], model: LazyModel): Seq[Constraint] = Seq()

  //a helper method
  //TODO: this should also handle reals
  protected def doesSatisfyExpr(expr: Expr, model: LazyModel): Boolean = {
    val compModel = variablesOf(expr).map { k => k -> model(k) }.toMap
    defaultEval.eval(expr, new Model(compModel)).result match {
      case Some(BooleanLiteral(true)) => true
      case _                          => false
    }
  }

  def splitVC(fd: FunDef) = {
    val (paramPart, rest, modCons) = ctrTracker.getVC(fd).toUnflatExpr
    if (ctx.usereals) {
      (IntLiteralToReal(paramPart), IntLiteralToReal(rest), modCons)
    } else (paramPart, rest, modCons)
  }

  /**
   * Counter-example guided solver
   */
  class CGSolver(funs: Seq[FunDef]) {

    //for miscellaneous things
    val trackNumericalDisjuncts = false
    var numericalDisjuncts = List[Expr]()

    case class FunData(vcSolver: Solver with TimeoutSolver, modelCons: (Model, DefaultEvaluator) => FlatModel,
        paramParts: Expr, simpleParts: Expr)
    val funInfos =
      if (useIncrementalSolvingForVCs) {
        funs.foldLeft(Map[FunDef, FunData]()) {
          case (acc, fd) =>
            val (paramPart, rest, modelCons) = splitVC(fd)
            if (hasReals(rest) && hasInts(rest))
              throw new IllegalStateException("Non-param Part has both integers and reals: " + rest)
            if (debugIncrementalVC) {
              assert(getTemplateVars(rest).isEmpty)
              println("For function: " + fd.id)
              println("Param part: " + paramPart)
            }
            if (!ctx.abort) { // this is required to ensure that solvers are not created after interrupts
              val vcSolver = solverFactory.getNewSolver()
              vcSolver.assertCnstr(rest)
              acc + (fd -> FunData(vcSolver, modelCons, paramPart, rest))
            } else acc
        }
      } else Map[FunDef, FunData]()

    def free = {
      if (useIncrementalSolvingForVCs)
        funInfos.foreach(entry => entry._2.vcSolver.free)
      if (trackNumericalDisjuncts)
        this.numericalDisjuncts = List[Expr]()
    }

    //state for minimization
    var minStarted = false
    var minStartTime: Long = 0
    var minimized = false

    def minimizationInProgress {
      if (!minStarted) {
        minStarted = true
        minStartTime = System.currentTimeMillis()
      }
    }

    def minimizationCompleted {
      minStarted = false
      val mintime = (System.currentTimeMillis() - minStartTime)
      /*Stats.updateCounterTime(mintime, "minimization-time", "procs")
    		Stats.updateCumTime(mintime, "Total-Min-Time")*/
    }

    def solveUNSAT(initModel: Model): (Option[Model], Option[Set[Call]], Model) = solveUNSAT(initModel, tru, Seq(), Set())

    def solveUNSAT(model: Model, inputCtr: Expr, solvedDisjs: Seq[Expr], seenCalls: Set[Call]): (Option[Model], Option[Set[Call]], Model) = {
      if (verbose) {
        reporter.info("Candidate invariants")
        val candInvs = getAllInvariants(model)
        candInvs.foreach((entry) => reporter.info(entry._1.id + "-->" + entry._2))
      }
      val (res, newCtr, newModel, newdisjs, newcalls) = invalidateSATDisjunct(inputCtr, model)
      res match {
        case _ if ctx.abort =>
          (None, None, model)
        case None =>
          //here, we cannot proceed and have to return unknown
          //However, we can return the calls that need to be unrolled
          (None, Some(seenCalls ++ newcalls), model)
        case Some(false) =>
          //here, the vcs are unsatisfiable when instantiated with the invariant
          if (minimizer.isDefined) {
            //for stats
            minimizationInProgress
            if (minimized) {
              minimizationCompleted
              (Some(model), None, model)
            } else {
              val minModel = minimizer.get(inputCtr, model)
              minimized = true
              if (minModel == model) {
                minimizationCompleted
                (Some(model), None, model)
              } else {
                solveUNSAT(minModel, inputCtr, solvedDisjs, seenCalls)
              }
            }
          } else {
            (Some(model), None, model)
          }
        case Some(true) =>
          //here, we have found a new candidate invariant. Hence, the above process needs to be repeated
          minimized = false
          solveUNSAT(newModel, newCtr, solvedDisjs ++ newdisjs, seenCalls ++ newcalls)
      }
    }

    //TODO: this code does too much imperative update.
    //TODO: use guards to block a path and not use the path itself
    def invalidateSATDisjunct(inputCtr: Expr, model: Model): (Option[Boolean], Expr, Model, Seq[Expr], Set[Call]) = {

      val tempIds = model.map(_._1)
      val tempVarMap: Map[Expr, Expr] = model.map((elem) => (elem._1.toVariable, elem._2)).toMap
      val inputSize = atomNum(inputCtr)

      var disjsSolvedInIter = Seq[Expr]()
      var callsInPaths = Set[Call]()
      var conflictingFuns = funs.toSet
      //mapping from the functions to the counter-example paths that were seen
      var seenPaths = MutableMap[FunDef, Seq[Expr]]()
      def updateSeenPaths(fd: FunDef, cePath: Expr): Unit = {
        if (seenPaths.contains(fd)) {
          seenPaths.update(fd, cePath +: seenPaths(fd))
        } else {
          seenPaths += (fd -> Seq(cePath))
        }
      }

      def invalidateDisjRecr(prevCtr: Expr): (Option[Boolean], Expr, Model) = {

        Stats.updateCounter(1, "disjuncts")

        var blockedCEs = false
        var confFunctions = Set[FunDef]()
        var confDisjuncts = Seq[Expr]()
        val newctrsOpt = conflictingFuns.foldLeft(Some(Seq()): Option[Seq[Expr]]) {
          case (None, _) => None
          case (Some(acc), fd) =>
            val disableCounterExs = if (seenPaths.contains(fd)) {
              blockedCEs = true
              Not(createOr(seenPaths(fd)))
            } else tru
            if (ctx.abort) None
            else
              getUNSATConstraints(fd, model, disableCounterExs) match {
                case None =>
                  None
                case Some(((disjunct, callsInPath), ctrsForFun)) =>
                  if (ctrsForFun == tru) Some(acc)
                  else {
                    confFunctions += fd
                    confDisjuncts :+= disjunct
                    callsInPaths ++= callsInPath
                    //instantiate the disjunct
                    val cePath = simplifyArithmetic(TemplateInstantiator.instantiate(disjunct, tempVarMap))
                    //some sanity checks
                    if (variablesOf(cePath).exists(TemplateIdFactory.IsTemplateIdentifier _))
                      throw new IllegalStateException("Found template identifier in counter-example disjunct: " + cePath)
                    updateSeenPaths(fd, cePath)
                    Some(acc :+ ctrsForFun)
                  }
              }
        }
        newctrsOpt match {
          case None =>
            // give up, the VC cannot be decided
            (None, tru, Model.empty)
          case Some(newctrs) =>
            //update conflicting functions
            conflictingFuns = confFunctions
            if (newctrs.isEmpty) {
              if (!blockedCEs) {
                //yes, hurray,found an inductive invariant
                (Some(false), prevCtr, model)
              } else {
                //give up, only hard paths remaining
                reporter.info("- Exhausted all easy paths !!")
                reporter.info("- Number of remaining hard paths: " + seenPaths.values.foldLeft(0)((acc, elem) => acc + elem.size))
                //TODO: what to unroll here ?
                (None, tru, Model.empty)
              }
            } else {
              //check that the new constraints does not have any reals
              val newPart = createAnd(newctrs)
              val newSize = atomNum(newPart)
              Stats.updateCounterStats((newSize + inputSize), "NLsize", "disjuncts")
              if (verbose)
                reporter.info("# of atomic predicates: " + newSize + " + " + inputSize)
              val combCtr = And(prevCtr, newPart)
              val (res, newModel) = farkasSolver.solveFarkasConstraints(combCtr)
              res match {
                case _ if ctx.abort =>
                  // stop immediately
                  (None, tru, Model.empty)
                case None => {
                  //here we have timed out while solving the non-linear constraints
                  if (verbose)
                    if (!disableCegis)
                      reporter.info("NLsolver timed-out on the disjunct... starting cegis phase...")
                    else
                      reporter.info("NLsolver timed-out on the disjunct... blocking this disjunct...")
                  if (!disableCegis) {
                    val (cres, cctr, cmodel) = solveWithCegis(tempIds.toSet, createOr(confDisjuncts), inputCtr, Some(model))
                    cres match {
                      case Some(true) => {
                        disjsSolvedInIter ++= confDisjuncts
                        (Some(true), And(inputCtr, cctr), cmodel)
                      }
                      case Some(false) => {
                        disjsSolvedInIter ++= confDisjuncts
                        //here also return the calls that needs to be unrolled
                        (None, fls, Model.empty)
                      }
                      case _ => {
                        if (verbose) reporter.info("retrying...")
                        Stats.updateCumStats(1, "retries")
                        //disable this disjunct and retry but, use the inputCtrs + the constraints generated by cegis from the next iteration
                        invalidateDisjRecr(And(inputCtr, cctr))
                      }
                    }
                  } else {
                    if (verbose) reporter.info("retrying...")
                    Stats.updateCumStats(1, "retries")
                    invalidateDisjRecr(inputCtr)
                  }
                }
                case Some(false) => {
                  //reporter.info("- Number of explored paths (of the DAG) in this unroll step: " + exploredPaths)
                  disjsSolvedInIter ++= confDisjuncts
                  (None, fls, Model.empty)
                }
                case Some(true) => {
                  disjsSolvedInIter ++= confDisjuncts
                  //new model may not have mappings for all the template variables, hence, use the mappings from earlier models
                  val compModel = new Model(tempIds.map((id) => {
                    if (newModel.isDefinedAt(id))
                      (id -> newModel(id))
                    else
                      (id -> model(id))
                  }).toMap)
                  (Some(true), combCtr, compModel)
                }
              }
            }
        }
      }
      val (res, newctr, newmodel) = invalidateDisjRecr(inputCtr)
      (res, newctr, newmodel, disjsSolvedInIter, callsInPaths)
    }

    def solveWithCegis(tempIds: Set[Identifier], expr: Expr, precond: Expr, initModel: Option[Model]): (Option[Boolean], Expr, Model) = {
      val cegisSolver = new CegisCore(ctx, program, timeout.toInt, NLTemplateSolver.this)
      val (res, ctr, model) = cegisSolver.solve(tempIds, expr, precond, solveAsInt = false, initModel)
      if (res.isEmpty)
        reporter.info("cegis timed-out on the disjunct...")
      (res, ctr, model)
    }

    protected def instantiateTemplate(e: Expr, tempVarMap: Map[Expr, Expr]): Expr = {
      if (ctx.usereals) replace(tempVarMap, e)
      else
        simplifyArithmetic(TemplateInstantiator.instantiate(e, tempVarMap))
    }

    /**
     * Constructs a quantifier-free non-linear constraint for unsatisfiability
     */
    def getUNSATConstraints(fd: FunDef, inModel: Model, disableCounterExs: Expr): Option[((Expr, Set[Call]), Expr)] = {

      val tempVarMap: Map[Expr, Expr] = inModel.map((elem) => (elem._1.toVariable, elem._2)).toMap
      val (solver, instExpr, modelCons) =
        if (useIncrementalSolvingForVCs) {
          val funData = funInfos(fd)
          val instParamPart = instantiateTemplate(funData.paramParts, tempVarMap)
          (funData.vcSolver, And(instParamPart, disableCounterExs), funData.modelCons)
        } else {
          val (paramPart, rest, modCons) = ctrTracker.getVC(fd).toUnflatExpr
          val instPart = instantiateTemplate(paramPart, tempVarMap)
          (solverFactory.getNewSolver(), createAnd(Seq(rest, instPart, disableCounterExs)), modCons)
        }
      //For debugging
      if (dumpInstantiatedVC) {
        val filename = "vcInst-" + FileCountGUID.getID
        val wr = new PrintWriter(new File(filename+".txt"))
        val fullExpr =
          if (useIncrementalSolvingForVCs) {
            And(funInfos(fd).simpleParts, instExpr)
          } else instExpr
        wr.println("Function name: " + fd.id+" \nFormula expr: ")
        ExpressionTransformer.PrintWithIndentation(wr, fullExpr)
        wr.close()
      }
      if(debugUnflattening){
        ctrTracker.getVC(fd).checkUnflattening(tempVarMap,
            SimpleSolverAPI(SolverFactory(() => solverFactory.getNewSolver())),
            defaultEval)
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
            solver.pop()
            solRes
          } else
            SimpleSolverAPI(SolverFactory(() => solver)).solveSAT(instExpr)
        } { vccTime =>
          if (verbose) reporter.info("checked VC inst... in " + vccTime / 1000.0 + "s")
          updateCounterTime(vccTime, "VC-check-time", "disjuncts")
          updateCumTime(vccTime, "TotalVCCTime")
        }
      //for statistics
      if (trackCompressedVCCTime) {
        val compressedVC =
          unflatten(simplifyArithmetic(instantiateTemplate(
            ctrTracker.getVC(fd).eliminateBlockers, tempVarMap)))
        Stats.updateCounterStats(atomNum(compressedVC), "Compressed-VC-size", "disjuncts")
        time {
          SimpleSolverAPI(SolverFactory(() => solverFactory.getNewSolver())).solveSAT(compressedVC)
        } { compTime =>
          Stats.updateCumTime(compTime, "TotalCompressVCCTime")
          reporter.info("checked compressed VC... in " + compTime / 1000.0 + "s")
        }
      }
      res match {
        case None => None // cannot check satisfiability of VCinst !!
        case Some(false) =>
          Some(((fls, Set()), tru)) //do not generate any constraints
        case Some(true) =>
          //For debugging purposes.
          if (verbose) reporter.info("Function: " + fd.id + "--Found candidate invariant is not a real invariant! ")
          if (printCounterExample) {
            reporter.info("Model: " + packedModel)
          }
          //get the disjuncts that are satisfied
          val model = modelCons(packedModel, defaultEval)
          val (data, newctr) =
            time { generateCtrsFromDisjunct(fd, model) } { chTime =>
              updateCounterTime(chTime, "Disj-choosing-time", "disjuncts")
              updateCumTime(chTime, "Total-Choose-Time")
            }
          if (newctr == tru) throw new IllegalStateException("Cannot find a counter-example path!!")
          Some((data, newctr))
      }
    }

    protected def generateCtrsFromDisjunct(fd: FunDef, initModel: LazyModel): ((Expr, Set[Call]), Expr) = {

      val formula = ctrTracker.getVC(fd)
      //this picks the satisfiable disjunct of the VC modulo axioms
      val satCtrs = formula.pickSatDisjunct(formula.firstRoot, initModel)
      //for debugging
      if (debugChooseDisjunct || printPathToConsole || dumpPathAsSMTLIB || verifyInvariant) {
        val pathctrs = satCtrs.map(_.toExpr)
        val plainFormula = createAnd(pathctrs)
        val pathcond = simplifyArithmetic(plainFormula)

        if (debugChooseDisjunct) {
          satCtrs.filter(_.isInstanceOf[LinearConstraint]).map(_.toExpr).foreach((ctr) => {
            if (!doesSatisfyExpr(ctr, initModel))
              throw new IllegalStateException("Path ctr not satisfied by model: " + ctr)
          })
        }
        if (verifyInvariant) {
          println("checking invariant for path...")
          val sat = checkInvariant(pathcond, leonctx, program)
        }
        if (printPathToConsole) {
          //val simpcond = ExpressionTransformer.unFlatten(pathcond, variablesOf(pathcond).filterNot(TVarFactory.isTemporary _))
          val simpcond = pathcond
          println("Full-path: " + ScalaPrinter(simpcond))
          val filename = "full-path-" + FileCountGUID.getID + ".txt"
          val wr = new PrintWriter(new File(filename))
          ExpressionTransformer.PrintWithIndentation(wr, simpcond)
          println("Printed to file: " + filename)
          wr.flush()
          wr.close()
        }
        if (dumpPathAsSMTLIB) {
          val filename = "pathcond" + FileCountGUID.getID + ".smt2"
          toZ3SMTLIB(pathcond, filename, "QF_NIA", leonctx, program)
          println("Path dumped to: " + filename)
        }
      }

      var calls = Set[Call]()
      var adtExprs = Seq[Expr]()
      satCtrs.foreach {
        case t: Call                                => calls += t
        case t: ADTConstraint if (t.cons || t.sel) => adtExprs :+= t.expr
        // TODO: ignoring all set constraints here, fix this
        case _                                      => ;
      }
      val callExprs = calls.map(_.toExpr)

      val axiomCtrs = time {
        ctrTracker.specInstantiator.axiomsForCalls(formula, calls, initModel)
      } { updateCumTime(_, "Total-AxiomChoose-Time") }

      //here, handle theory operations by reducing them to axioms.
      //Note: uninterpreted calls/ADTs are handled below as they are more general. Here, we handle
      //other theory axioms like: multiplication, sets, arrays, maps etc.
      val theoryCtrs = time {
        axiomsForTheory(formula, calls, initModel)
      } { updateCumTime(_, "Total-TheoryAxiomatization-Time") }

      //Finally, eliminate UF/ADT
      // convert all adt constraints to 'cons' ctrs, and expand the model
      val selTrans = new SelectorToCons()
      val cons = selTrans.selToCons(adtExprs)
      val expModel = selTrans.getModel(initModel)
      // get constraints for UFADTs
      val callCtrs = time {
        (new UFADTEliminator(leonctx, program)).constraintsForCalls((callExprs ++ cons),
          linearEval.predEval(expModel)).map(ConstraintUtil.createConstriant _)
      } { updateCumTime(_, "Total-ElimUF-Time") }

      //exclude guards, separate calls and cons from the rest
      var lnctrs = Set[LinearConstraint]()
      var temps = Set[LinearTemplate]()
      (satCtrs ++ callCtrs ++ axiomCtrs ++ theoryCtrs).foreach {
        case t: LinearConstraint => lnctrs += t
        case t: LinearTemplate   => temps += t
        case _                   => ;
      }
      if (debugChooseDisjunct) {
        lnctrs.map(_.toExpr).foreach((ctr) => {
          if (!doesSatisfyExpr(ctr, expModel))
            throw new IllegalStateException("Ctr not satisfied by model: " + ctr)
        })
      }
      if (debugTheoryReduction) {
        val simpPathCond = createAnd((lnctrs ++ temps).map(_.template).toSeq)
        if (verifyInvariant) {
          println("checking invariant for simp-path...")
          checkInvariant(simpPathCond, leonctx, program)
        }
      }
      if (trackNumericalDisjuncts) {
        numericalDisjuncts :+= createAnd((lnctrs ++ temps).map(_.template).toSeq)
      }
      val (data, nlctr) = processNumCtrs(lnctrs.toSeq, temps.toSeq)
      ((data, calls), nlctr)
    }

    /**
     * Endpoint of the pipeline. Invokes the Farkas Lemma constraint generation.
     */
    def processNumCtrs(lnctrs: Seq[LinearConstraint], temps: Seq[LinearTemplate]): (Expr, Expr) = {
      //here we are invalidating A^~(B)
      if (temps.isEmpty) {
        //here ants ^ conseq is sat (otherwise we wouldn't reach here) and there is no way to falsify this path
        (createAnd(lnctrs.map(_.toExpr)), fls)
      } else {
        if (debugElimination) {
          //println("Path Constraints (before elim): "+(lnctrs ++ temps))
          if (verifyInvariant) {
            println("checking invariant for disjunct before elimination...")
            checkInvariant(createAnd((lnctrs ++ temps).map(_.template)), leonctx, program)
          }
        }
        //compute variables to be eliminated
        val ctrVars = lnctrs.foldLeft(Set[Identifier]())((acc, lc) => acc ++ variablesOf(lc.toExpr))
        val tempVars = temps.foldLeft(Set[Identifier]())((acc, lt) => acc ++ variablesOf(lt.template))
        val elimVars = ctrVars.diff(tempVars)
        // for debugging
        val debugger =
          if (debugElimination && verifyInvariant) {
            Some((ctrs: Seq[LinearConstraint]) => {
              val debugRes = checkInvariant(createAnd((ctrs ++ temps).map(_.template)), leonctx, program)
            })
          } else None
        val elimLnctrs = time {
          LinearConstraintUtil.apply1PRuleOnDisjunct(lnctrs, elimVars, debugger)
        } { updateCumTime(_, "ElimTime") }

        if (debugElimination) {
          println("Path constriants (after elimination): " + elimLnctrs)
          if (verifyInvariant) {
            println("checking invariant for disjunct after elimination...")
            checkInvariant(createAnd((elimLnctrs ++ temps).map(_.template)), leonctx, program)
          }
        }
        //for stats
        if (ctx.dumpStats) {
          var elimCtrCount = 0
          var elimCtrs = Seq[LinearConstraint]()
          var elimRems = Set[Identifier]()
          elimLnctrs.foreach((lc) => {
            val evars = variablesOf(lc.toExpr).intersect(elimVars)
            if (evars.nonEmpty) {
              elimCtrs :+= lc
              elimCtrCount += 1
              elimRems ++= evars
            }
          })
          Stats.updateCounterStats((elimVars.size - elimRems.size), "Eliminated-Vars", "disjuncts")
          Stats.updateCounterStats((lnctrs.size - elimLnctrs.size), "Eliminated-Atoms", "disjuncts")
          Stats.updateCounterStats(temps.size, "Param-Atoms", "disjuncts")
          Stats.updateCounterStats(lnctrs.size, "NonParam-Atoms", "disjuncts")
        }
        val newLnctrs = elimLnctrs.toSet.toSeq

        //TODO:Remove transitive facts. E.g. a <= b, b <= c, a <=c can be simplified by dropping a <= c
        //TODO: simplify the formulas and remove implied conjuncts if possible (note the formula is satisfiable, so there can be no inconsistencies)
        //e.g, remove: a <= b if we have a = b or if a < b
        //Also, enrich the rules for quantifier elimination: try z3 quantifier elimination on variables that have an equality.
        //TODO: Use the dependence chains in the formulas to identify what to assertionize
        // and what can never be implied by solving for the templates
        val disjunct = createAnd((newLnctrs ++ temps).map(_.template))
        val implCtrs = farkasSolver.constraintsForUnsat(newLnctrs, temps)
        //for debugging
        if (debugReducedFormula) {
          println("Final Path Constraints: " + disjunct)
          if (verifyInvariant) {
            println("checking invariant for final disjunct... ")
            checkInvariant(disjunct, leonctx, program)
          }
        }
        (disjunct, implCtrs)
      }
    }
  }
}
