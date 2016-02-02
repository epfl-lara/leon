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
import RealValuedExprEvaluator._
import Util._
import PredicateUtil._
import SolverUtil._

class NLTemplateSolver(ctx: InferenceContext, program: Program,
    rootFun: FunDef, ctrTracker: ConstraintTracker,
    minimizer: Option[(Expr, Model) => Model])
  extends TemplateSolver(ctx, rootFun, ctrTracker) {

  //flags controlling debugging
  val debugIncrementalVC = false
  val debugElimination = false
  val debugChooseDisjunct = false
  val debugTheoryReduction = false
  val debugAxioms = false
  val verifyInvariant = false
  val debugReducedFormula = false
  val trackUnpackedVCCTime = false

  //print flags
  val verbose = false
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
  private val useCVCToCheckVCs = true

  //this is private mutable state used by initialized during every call to 'solve' and used by 'solveUNSAT'
  protected var funcVCs = Map[FunDef, Expr]()
  //TODO: can incremental solving be trusted ? There were problems earlier.
  protected var vcSolvers = Map[FunDef, Solver with TimeoutSolver]()
  protected var paramParts = Map[FunDef, Expr]()
  protected var simpleParts = Map[FunDef, Expr]()
  private var lastFoundModel: Option[Model] = None

  //for miscellaneous things
  val trackNumericalDisjuncts = false
  var numericalDisjuncts = List[Expr]()

  protected def splitVC(fd: FunDef): (Expr, Expr) = {
    ctrTracker.getVC(fd).splitParamPart
  }

  def initVCSolvers = {
    funcVCs.keys.foreach { fd =>
      val (paramPart, rest) = if (ctx.usereals) {
        val (pp, r) = splitVC(fd)
        (IntLiteralToReal(pp), IntLiteralToReal(r))
      } else
        splitVC(fd)

      if (hasReals(rest) && hasInts(rest))
        throw new IllegalStateException("Non-param Part has both integers and reals: " + rest)

      if (!ctx.abort) { // this is required to ensure that solvers are not created after interrupts
        val vcSolver =
          if (this.useCVCToCheckVCs)
            new SMTLIBCVC4Solver(leonctx, program) with TimeoutSolver
          else
            new SMTLIBZ3Solver(leonctx, program) with TimeoutSolver
        vcSolver.assertCnstr(rest)

        if (debugIncrementalVC) {
          assert(getTemplateVars(rest).isEmpty)
          println("For function: " + fd.id)
          println("Param part: " + paramPart)
          /*vcSolver.check match {
        case Some(false) => throw new IllegalStateException("Non param-part is unsat "+rest)
        case _ => ;
      	}*/
        }
        vcSolvers += (fd -> vcSolver)
        paramParts += (fd -> paramPart)
        simpleParts += (fd -> rest)
      }
    }
  }

  def freeVCSolvers {
    vcSolvers.foreach(entry => entry._2.free)
  }

  /**
   * This function computes invariants belonging to the given templates incrementally.
   * The result is a mapping from function definitions to the corresponding invariants.
   */
  override def solve(tempIds: Set[Identifier], funcVCs: Map[FunDef, Expr]): (Option[Model], Option[Set[Call]]) = {
    //initialize vcs of functions
    this.funcVCs = funcVCs
    if (useIncrementalSolvingForVCs) {
      initVCSolvers
    }
    val initModel = if (this.startFromEarlierModel && lastFoundModel.isDefined) {
      val candModel = lastFoundModel.get
      new Model(tempIds.map(id =>
        (id -> candModel.getOrElse(id, simplestValue(id.getType)))).toMap)
    } else {
      new Model(tempIds.map((id) =>
        (id -> simplestValue(id.getType))).toMap)
    }
    val sol = solveUNSAT(initModel, tru, Seq(), Set())

    if (useIncrementalSolvingForVCs) {
      freeVCSolvers
    }
    //set lowerbound map
    //TODO: find a way to record lower bound stats
    /*if (ctx.tightBounds)
      SpecificStats.addLowerBoundStats(rootFun, minimizer.lowerBoundMap, "")*/
    //miscellaneous stuff
    if (trackNumericalDisjuncts) {
      this.numericalDisjuncts = List[Expr]()
    }
    sol
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

  def solveUNSAT(model: Model, inputCtr: Expr, solvedDisjs: Seq[Expr], seenCalls: Set[Call]): (Option[Model], Option[Set[Call]]) = {

    if (verbose) {
      reporter.info("Candidate invariants")
      val candInvs = getAllInvariants(model)
      candInvs.foreach((entry) => reporter.info(entry._1.id + "-->" + entry._2))
    }

    if (this.startFromEarlierModel) this.lastFoundModel = Some(model)

    val (res, newCtr, newModel, newdisjs, newcalls) = invalidateSATDisjunct(inputCtr, model)
    res match {
      case _ if ctx.abort =>
        (None, None)
      case None => {
        //here, we cannot proceed and have to return unknown
        //However, we can return the calls that need to be unrolled
        (None, Some(seenCalls ++ newcalls))
      }
      case Some(false) => {
        //here, the vcs are unsatisfiable when instantiated with the invariant
        if (minimizer.isDefined) {
          //for stats
          minimizationInProgress
          if (minimized) {
            minimizationCompleted
            (Some(model), None)
          } else {
            val minModel = minimizer.get(inputCtr, model)
            minimized = true
            if (minModel == model) {
              minimizationCompleted
              (Some(model), None)
            } else {
              solveUNSAT(minModel, inputCtr, solvedDisjs, seenCalls)
            }
          }
        } else {
          (Some(model), None)
        }
      }
      case Some(true) => {
        //here, we have found a new candidate invariant. Hence, the above process needs to be repeated
        minimized = false
        solveUNSAT(newModel, newCtr, solvedDisjs ++ newdisjs, seenCalls ++ newcalls)
      }
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
    var conflictingFuns = funcVCs.keySet
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
            //here we need to solve for the newctrs + inputCtrs
            val combCtr = And(prevCtr, newPart)
            val (res, newModel) = farkasSolver.solveFarkasConstraints(combCtr)
            res match {
              case _ if ctx.abort =>
                 // stop immediately
                (None, tru, Model.empty)
              case None => {
                //here we have timed out while solving the non-linear constraints
                if (verbose)
                  if (!this.disableCegis)
                    reporter.info("NLsolver timed-out on the disjunct... starting cegis phase...")
                  else
                    reporter.info("NLsolver timed-out on the disjunct... blocking this disjunct...")
                if (!this.disableCegis) {
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

    val cegisSolver = new CegisCore(ctx, program, timeout.toInt, this)
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
    val solver =
      if (this.useIncrementalSolvingForVCs) vcSolvers(fd)
      else new SMTLIBZ3Solver(leonctx, program) with TimeoutSolver
    val instExpr = if (this.useIncrementalSolvingForVCs) {
      val instParamPart = instantiateTemplate(this.paramParts(fd), tempVarMap)
      And(instParamPart, disableCounterExs)
    } else {
      val instVC = instantiateTemplate(funcVCs(fd), tempVarMap)
      And(instVC, disableCounterExs)
    }
    //For debugging
    if (this.dumpInstantiatedVC) {
      // println("Plain vc: "+funcVCs(fd))
      val wr = new PrintWriter(new File("formula-dump.txt"))
      val fullExpr = if (this.useIncrementalSolvingForVCs) {
        And(simpleParts(fd), instExpr)
      } else
        instExpr
      // println("Instantiated VC of " + fd.id + " is: " + fullExpr)
      wr.println("Function name: " + fd.id)
      wr.println("Formula expr: ")
      ExpressionTransformer.PrintWithIndentation(wr, fullExpr)
      wr.flush()
      wr.close()
    }
    if (hasMixedIntReals(instExpr)) {
      throw new IllegalStateException("Instantiated VC of " + fd.id + " contains mixed integer/reals: " + instExpr)
    }

    //reporter.info("checking VC inst ...")
    var t1 = System.currentTimeMillis()
    solver.setTimeout(timeout * 1000)
    val (res, model) = if (this.useIncrementalSolvingForVCs) {
      solver.push
      solver.assertCnstr(instExpr)
      // new InterruptOnSignal(solver).interruptOnSignal(ctx.abort)(
      val solRes = solver.check match {
        case _ if ctx.abort =>
          (None, Model.empty)
        case r @ Some(true) =>
          (r, solver.getModel)
        case r => (r, Model.empty)
      }
      solver.pop()
      solRes
    } else {
      SimpleSolverAPI(SolverFactory(() => solver)).solveSAT(instExpr)
    }
    val vccTime = (System.currentTimeMillis() - t1)

    if (verbose) reporter.info("checked VC inst... in " + vccTime / 1000.0 + "s")
    Stats.updateCounterTime(vccTime, "VC-check-time", "disjuncts")
    Stats.updateCumTime(vccTime, "TotalVCCTime")

    //for debugging
    if (this.trackUnpackedVCCTime) {
      val upVCinst = simplifyArithmetic(TemplateInstantiator.instantiate(ctrTracker.getVC(fd).unpackedExpr, tempVarMap))
      Stats.updateCounterStats(atomNum(upVCinst), "UP-VC-size", "disjuncts")

      t1 = System.currentTimeMillis()
      val (res2, _) = SimpleSolverAPI(SolverFactory(() => new SMTLIBZ3Solver(leonctx, program))).solveSAT(upVCinst)
      val unpackedTime = System.currentTimeMillis() - t1
      if (res != res2) {
        throw new IllegalStateException("Unpacked VC produces different result: " + upVCinst)
      }
      Stats.updateCumTime(unpackedTime, "TotalUPVCCTime")
      reporter.info("checked UP-VC inst... in " + unpackedTime / 1000.0 + "s")
    }

    t1 = System.currentTimeMillis()
    res match {
      case None => {
        //throw new IllegalStateException("cannot check the satisfiability of " + funcVCs(fd))
        None
      }
      case Some(false) => {
        //do not generate any constraints
        Some(((fls, Set()), tru))
      }
      case Some(true) => {
        //For debugging purposes.
        if (verbose) reporter.info("Function: " + fd.id + "--Found candidate invariant is not a real invariant! ")
        if (this.printCounterExample) {
          reporter.info("Model: " + model)
        }
        //get the disjuncts that are satisfied
        val (data, newctr) = generateCtrsFromDisjunct(fd, model)
        if (newctr == tru)
          throw new IllegalStateException("Cannot find a counter-example path!!")

        val t2 = System.currentTimeMillis()
        Stats.updateCounterTime((t2 - t1), "Disj-choosing-time", "disjuncts")
        Stats.updateCumTime((t2 - t1), "Total-Choose-Time")

        Some((data, newctr))
      }
    }
  }

  lazy val evaluator = new DefaultEvaluator(leonctx, program) //as of now used only for debugging
  //a helper method
  //TODO: this should also handle reals
  protected def doesSatisfyModel(expr: Expr, model: Model): Boolean = {
    evaluator.eval(expr, model).result match {
      case Some(BooleanLiteral(true)) => true
      case _ => false
    }
  }

  /**
   * Evaluator for a predicate that is a simple equality/inequality between two variables
   */
  protected def predEval(model: Model): (Expr => Boolean) = {
    if (ctx.usereals) realEval(model)
    else intEval(model)
  }

  protected def intEval(model: Model): (Expr => Boolean) = {
    def modelVal(id: Identifier): BigInt = {
      val InfiniteIntegerLiteral(v) = model(id)
      v
    }
    def eval: (Expr => Boolean) = {
      case And(args) => args.forall(eval)
      // case Iff(Variable(id1), Variable(id2)) => model(id1) == model(id2)
      case Equals(Variable(id1), Variable(id2)) => model(id1) == model(id2) //note: ADTs can also be compared for equality
      case LessEquals(Variable(id1), Variable(id2)) => modelVal(id1) <= modelVal(id2)
      case GreaterEquals(Variable(id1), Variable(id2)) => modelVal(id1) >= modelVal(id2)
      case GreaterThan(Variable(id1), Variable(id2)) => modelVal(id1) > modelVal(id2)
      case LessThan(Variable(id1), Variable(id2)) => modelVal(id1) < modelVal(id2)
      case e => throw new IllegalStateException("Predicate not handled: " + e)
    }
    eval
  }

  protected def realEval(model: Model): (Expr => Boolean) = {
    def modelVal(id: Identifier): FractionalLiteral = {
      //println("Identifier: "+id)
      model(id).asInstanceOf[FractionalLiteral]
    }
    {
      case Equals(Variable(id1), Variable(id2)) => model(id1) == model(id2) //note: ADTs can also be compared for equality
      case e@Operator(Seq(Variable(id1), Variable(id2)), op) if (e.isInstanceOf[LessThan]
        || e.isInstanceOf[LessEquals] || e.isInstanceOf[GreaterThan]
        || e.isInstanceOf[GreaterEquals]) => {
        evaluateRealPredicate(op(Seq(modelVal(id1), modelVal(id2))))
      }
      case e => throw new IllegalStateException("Predicate not handled: " + e)
    }
  }

  /**
   * This solver does not use any theories other than UF/ADT. It assumes that other theories are axiomatized in the VC.
   * This method can overloaded by the subclasses.
   */
  protected def axiomsForTheory(formula: Formula, calls: Set[Call], model: Model): Seq[Constraint] = Seq()

  protected def generateCtrsFromDisjunct(fd: FunDef, model: Model): ((Expr, Set[Call]), Expr) = {

    val formula = ctrTracker.getVC(fd)
    //this picks the satisfiable disjunct of the VC modulo axioms
    val satCtrs = formula.pickSatDisjunct(formula.firstRoot, model)
    //for debugging
    if (this.debugChooseDisjunct || this.printPathToConsole || this.dumpPathAsSMTLIB || this.verifyInvariant) {
      val pathctrs = satCtrs.map(_.toExpr)
      val plainFormula = createAnd(pathctrs)
      val pathcond = simplifyArithmetic(plainFormula)

      if (this.debugChooseDisjunct) {
        satCtrs.filter(_.isInstanceOf[LinearConstraint]).map(_.toExpr).foreach((ctr) => {
          if (!doesSatisfyModel(ctr, model))
            throw new IllegalStateException("Path ctr not satisfied by model: " + ctr)
        })
      }

      if (this.verifyInvariant) {
        println("checking invariant for path...")
        val sat = checkInvariant(pathcond, leonctx, program)
      }

      if (this.printPathToConsole) {
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

      if (this.dumpPathAsSMTLIB) {
        val filename = "pathcond" + FileCountGUID.getID + ".smt2"
        toZ3SMTLIB(pathcond, filename, "QF_NIA", leonctx, program)
        println("Path dumped to: " + filename)
      }
    }

    var calls = Set[Call]()
    var cons = Set[Expr]()
    satCtrs.foreach {
      case t: Call => calls += t
      case t: ADTConstraint if (t.cons.isDefined) => cons += t.cons.get
      // TODO: ignoring all set constraints here, fix this
      case _ => ;
    }
    val callExprs = calls.map(_.toExpr)

    var t1 = System.currentTimeMillis()
    val axiomCtrs = ctrTracker.specInstantiator.axiomsForCalls(formula, calls, model)
    var t2 = System.currentTimeMillis()
    Stats.updateCumTime((t2 - t1), "Total-AxiomChoose-Time")

    //here, handle theory operations by reducing them to axioms.
    //Note: uninterpreted calls/ADTs are handled below as they are more general. Here, we handle
    //other theory axioms like: multiplication, sets, arrays, maps etc.
    t1 = System.currentTimeMillis()
    val theoryCtrs = axiomsForTheory(formula, calls, model)
    t2 = System.currentTimeMillis()
    Stats.updateCumTime((t2 - t1), "Total-TheoryAxiomatization-Time")

    //Finally, eliminate UF/ADT
    t1 = System.currentTimeMillis()
    val callCtrs = (new UFADTEliminator(leonctx, program)).constraintsForCalls((callExprs ++ cons),
      predEval(model)).map(ConstraintUtil.createConstriant _)
    t2 = System.currentTimeMillis()
    Stats.updateCumTime((t2 - t1), "Total-ElimUF-Time")

    //exclude guards, separate calls and cons from the rest
    var lnctrs = Set[LinearConstraint]()
    var temps = Set[LinearTemplate]()
    (satCtrs ++ callCtrs ++ axiomCtrs ++ theoryCtrs).foreach {
      case t: LinearConstraint => lnctrs += t
      case t: LinearTemplate => temps += t
      case _ => ;
    }

    if (this.debugChooseDisjunct) {
      lnctrs.map(_.toExpr).foreach((ctr) => {
        if (!doesSatisfyModel(ctr, model))
          throw new IllegalStateException("Ctr not satisfied by model: " + ctr)
      })
    }

    if (this.debugTheoryReduction) {
      val simpPathCond = createAnd((lnctrs ++ temps).map(_.template).toSeq)
      if (this.verifyInvariant) {
        println("checking invariant for simp-path...")
        checkInvariant(simpPathCond, leonctx, program)
      }
    }

    if (this.trackNumericalDisjuncts) {
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

      if (this.debugElimination) {
        //println("Path Constraints (before elim): "+(lnctrs ++ temps))
        if (this.verifyInvariant) {
          println("checking invariant for disjunct before elimination...")
          checkInvariant(createAnd((lnctrs ++ temps).map(_.template)), leonctx, program)
        }
      }
      //compute variables to be eliminated
      val t1 = System.currentTimeMillis()
      val ctrVars = lnctrs.foldLeft(Set[Identifier]())((acc, lc) => acc ++ variablesOf(lc.toExpr))
      val tempVars = temps.foldLeft(Set[Identifier]())((acc, lt) => acc ++ variablesOf(lt.template))
      val elimVars = ctrVars.diff(tempVars)

      val debugger = if (debugElimination && verifyInvariant) {
        Some((ctrs: Seq[LinearConstraint]) => {
          //println("checking disjunct before elimination...")
          //println("ctrs: "+ctrs)
          val debugRes = checkInvariant(createAnd((ctrs ++ temps).map(_.template)), leonctx, program)
        })
      } else None
      val elimLnctrs = LinearConstraintUtil.apply1PRuleOnDisjunct(lnctrs, elimVars, debugger)
      val t2 = System.currentTimeMillis()

      if (this.debugElimination) {
        println("Path constriants (after elimination): " + elimLnctrs)
        if (this.verifyInvariant) {
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
        Stats.updateCumTime((t2 - t1), "ElimTime")
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
      if (this.debugReducedFormula) {
        println("Final Path Constraints: " + disjunct)
        if (this.verifyInvariant) {
          println("checking invariant for final disjunct... ")
          checkInvariant(disjunct, leonctx, program)
        }
      }

      (disjunct, implCtrs)
    }
  }
}
