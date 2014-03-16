package leon
package invariant

import scala.util.Random
import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import solvers.{ Solver, TimeoutSolver }
import solvers.z3.FairZ3Solver
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.mutable.{ Map => MutableMap }
import leon.evaluators._
import java.io._
import leon.solvers.z3.UninterpretedZ3Solver
import leon.LeonContext
import leon.LeonOptionDef
import leon.LeonPhase
import leon.LeonValueOption
import leon.ListValue
import leon.Reporter
import leon.verification.DefaultTactic
import leon.verification.ExtendedVC
import leon.verification.Tactic
import leon.verification.VerificationReport
import leon.solvers.SimpleSolverAPI
import leon.solvers.z3.UIFZ3Solver
import leon.invariant._
import leon.purescala.UndirectedGraph
import scala.util.control.Breaks._
import leon.solvers._
import leon.purescala.ScalaPrinter
import leon.plugin.DepthInstPhase

class NLTemplateSolver(context: LeonContext, program: Program, rootFun: FunDef,
  ctrTracker: ConstraintTracker, tempFactory: TemplateFactory, timeout: Int, tightBounds: Boolean) 
  extends TemplateSolver(context, program, rootFun, ctrTracker, tempFactory, timeout) {

  //flags controlling debugging  
  val debugIncrementalVC = false
  val debugElimination = false
  val debugChooseDisjunct = false
  val debugAxioms = false
  val verifyInvariant = false
  val debugReducedFormula = false
  val trackUnpackedVCCTime = false

  //print flags
  val printCounterExample = false
  val printPathToConsole = false
  val dumpPathAsSMTLIB = false
  val dumpNLCtrsAsSMTLIB = false
  val printCallConstriants = false
  val printReducedFormula = false
  val dumpInstantiatedVC = false
  
  //flag controlling behavior
  private val farkasSolver = new FarkasLemmaSolver()
  private val minimizer = new Minimizer(context, program, timeout)  
  private val disableCegis = true
  private val solveAsBitvectors = false
  private val bvsize = 5
  private val useIncrementalSolvingForVCs = true
  private val useIncrementalSolvingForNLctrs = false
  
  //this is private mutable state used by initialized during every call to 'solve' and used by 'solveUNSAT'
  private var funcVCs = Map[FunDef, Expr]()  
  //TODO: can incremental solving be trusted ? There were problems earlier.
  private var vcSolvers = Map[FunDef, UIFZ3Solver]()
  private var paramParts = Map[FunDef, Expr]()   
  private var solverWithNLctrs : UIFZ3Solver = null //not used as of now
    
  def initVCSolvers  {
    funcVCs.keys.foreach(fd => {
      val vcFormula = ctrTracker.getVC(fd)
      val (paramPart, rest) = vcFormula.splitParamPart

      if (debugIncrementalVC) {
        assert(InvariantUtil.getTemplateVars(rest).isEmpty)
        println("For function: "+fd.id)        
        println("Param part: "+paramPart)
        //println("Rest: "+rest)        
      }
      val vcSolver = new UIFZ3Solver(context, program)
      vcSolver.assertCnstr(rest)
      vcSolvers += (fd -> vcSolver)
      paramParts += (fd -> paramPart)
    })
  }
  
  def freeVCSolvers  {
    vcSolvers.foreach(entry => entry._2.free)
  }

  /**
   * This function computes invariants belonging to the given templates incrementally.
   * The result is a mapping from function definitions to the corresponding invariants.
   */
  override def solve(tempIds: Set[Identifier], funcVCs: Map[FunDef, Expr]): (Option[Map[FunDef, Expr]], Option[Set[Call]]) = {

    //initialize vcs of functions
    this.funcVCs = funcVCs
    
    if(useIncrementalSolvingForVCs) {
      initVCSolvers
    } 
    val initModel = {
      val simplestModel = tempIds.map((id) => (id -> simplestValue(id.toVariable))).toMap
      simplestModel
    }
    val sol = solveUNSAT(initModel, tru, Seq(), Set())
        
    if(useIncrementalSolvingForVCs) {
      freeVCSolvers
    }

    //set lowerbound map
    if (this.tightBounds)
      SpecificStats.addLowerBoundStats(rootFun, minimizer.lowerBoundMap, "")
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
    Stats.updateCounterTime(mintime, "minimization-time", "procs")
    Stats.updateCumTime(mintime, "Total-Min-Time")
  }

  def solveUNSAT(model: Map[Identifier, Expr], inputCtr: Expr, solvedDisjs: Seq[Expr], seenCalls: Set[Call])
  : (Option[Map[FunDef, Expr]], Option[Set[Call]]) = {

    println("candidate Invariants")
    val candInvs = getAllInvariants(model)
    candInvs.foreach((entry) => println(entry._1.id + "-->" + entry._2))

    /*//TODO: There is a serious bug in z3 in incremental solving. The following code is for reproducing the bug            
    if (this.debugIncremental) {
      solverWithCtr.assertCnstr(inputCtr)
    }*/

    val (res, newCtr, newModel, newdisjs, newcalls) = invalidateSATDisjunct(inputCtr, model)
    res match {
      case None => {
        //here, we cannot proceed and have to return unknown
        //However, we can return the calls that need to be unrolled                       
        (None, Some(seenCalls ++ newcalls))
      }
      case Some(false) => {
        //here, the vcs are unsatisfiable when instantiated with the invariant
        val template = tempFactory.getTemplate(rootFun)
        //TODO: need to assert that the templates are time templates
        if (tightBounds && template.isDefined) {
          //for stats
          minimizationInProgress

          if (minimized) {
            minimizationCompleted
            (Some(getAllInvariants(model)), None)
          } else {
            val minModel = minimizer.tightenTimeBounds(template.get, inputCtr, model)
            minimized = true
            if (minModel == model) {
              minimizationCompleted
              (Some(getAllInvariants(model)), None)
            } else {
              solveUNSAT(minModel, inputCtr, solvedDisjs, seenCalls)
            }
          }
        } else {
          (Some(getAllInvariants(model)), None)
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
  def invalidateSATDisjunct(inputCtr: Expr, model: Map[Identifier, Expr])
  : (Option[Boolean], Expr, Map[Identifier, Expr], Seq[Expr], Set[Call]) = {

    val tempIds = model.keys
    val tempVarMap: Map[Expr, Expr] = model.map((elem) => (elem._1.toVariable, elem._2)).toMap
    val inputSize = InvariantUtil.atomNum(inputCtr)

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

    def invalidateDisjRecr(prevCtr: Expr): (Option[Boolean], Expr, Map[Identifier, Expr]) = {

      Stats.updateCounter(1, "disjuncts")

      var blockedCEs = false
      var confFunctions = Set[FunDef]()
      var confDisjuncts = Seq[Expr]()

      val newctrs = conflictingFuns.foldLeft(Seq[Expr]())((acc, fd) => {

        //val instVC = simplifyArithmetic(TemplateInstantiator.instantiate(funcVCs(fd), tempVarMap))
        //here, block the counter-examples seen thus far for the function        
        //val instVCmodCE = And(instVC, disableCounterExs)
        //val (data, ctrsForFun) = getNLConstraints(fd, instVCmodCE)
        val disableCounterExs = if (seenPaths.contains(fd)) {
          blockedCEs = true
          Not(Or(seenPaths(fd)))
        } else tru
        val (data, ctrsForFun) = getUNSATConstraints(fd, model, disableCounterExs)
        val (disjunct, callsInPath) = data
        if (ctrsForFun == tru) acc
        else {
          confFunctions += fd
          confDisjuncts :+= disjunct
          callsInPaths ++= callsInPath
          //instantiate the disjunct
          val cePath = simplifyArithmetic(TemplateInstantiator.instantiate(disjunct, tempVarMap))

          //some sanity checks
          if (variablesOf(cePath).exists(TemplateIdFactory.IsTemplateIdentifier _))
            throw IllegalStateException("Found template identifier in counter-example disjunct: " + cePath)

          updateSeenPaths(fd, cePath)
          acc :+ ctrsForFun
        }
      })
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
          (None, tru, Map())
        }
      } else {

        val newPart = And(newctrs)
        val newSize = InvariantUtil.atomNum(newPart)
        Stats.updateCounterStats((newSize + inputSize), "NLsize", "disjuncts")
        println("# of atomic predicates: " + newSize + " + " + inputSize)

        /*if (this.debugIncremental)
          solverWithCtr.assertCnstr(newPart)*/

        //here we need to solve for the newctrs + inputCtrs
        val combCtr = And(prevCtr, newPart)
        val (res, newModel) = solveNLConstraints(combCtr)

        res match {
          case None => {
            //here we have timed out while solving the non-linear constraints
            if (!this.disableCegis)
              reporter.info("NLsolver timed-out on the disjunct... starting cegis phase...")
            else
              reporter.info("NLsolver timed-out on the disjunct... blocking this disjunct...")

            if (!this.disableCegis) {
              val (cres, cctr, cmodel) = solveWithCegis(tempIds.toSet, Or(confDisjuncts), inputCtr, Some(model))
              cres match {
                case Some(true) => {
                  disjsSolvedInIter ++= confDisjuncts
                  (Some(true), And(inputCtr, cctr), cmodel)
                }
                case Some(false) => {
                  disjsSolvedInIter ++= confDisjuncts
                  //here also return the calls that needs to be unrolled
                  (None, fls, Map())
                }
                case _ => {
                  reporter.info("retrying...")
                  Stats.updateCumStats(1, "retries")
                  //disable this disjunct and retry but, use the inputCtrs + the constraints generated by cegis from the next iteration
                  invalidateDisjRecr(And(inputCtr, cctr))
                }
              }
            } else {
              reporter.info("retrying...")
              Stats.updateCumStats(1, "retries")
              invalidateDisjRecr(inputCtr)
            }
          }
          case Some(false) => {
            //reporter.info("- Number of explored paths (of the DAG) in this unroll step: " + exploredPaths)
            disjsSolvedInIter ++= confDisjuncts
            (None, fls, Map())
          }
          case Some(true) => {

            /* val denomZero = newModel.values.exists((e: Expr) => e match {
              case RealLiteral(_, 0) => true
              case _ => false
            })
            if (denomZero){
              reporter.info("The model has a divide by zero")
              throw IllegalStateException("")
            }
          */
            //TODO: There is a serious bug in z3 in incremental solving. The following code is for reproducing the bug            
            /*if (debugIncremental) {
              println("Found a model1: " + newModel)
              val model2 = solverWithCtr.getModel
              println("Found a model2: " + model2)
              solverWithCtr.push()
              solverWithCtr.assertCnstr(InvariantUtil.modelToExpr(model2))

              val fn2 = "z3formula-withModel-" + FileCountGUID.fileCount + ".smt"
              val pwr = new PrintWriter(fn2)
              pwr.println(solverWithCtr.ctrsToString("QF_NRA"))
              pwr.flush()
              pwr.close()
              println("Formula & Model printed to File: " + fn2)

              solverWithCtr.pop()
            }
*/
            disjsSolvedInIter ++= confDisjuncts
            //new model may not have mappings for all the template variables, hence, use the mappings from earlier models            
            val compModel = tempIds.map((id) => {
              if (newModel.contains(id))
                (id -> newModel(id))
              else
                (id -> model(id))
            }).toMap
            (Some(true), combCtr, compModel)
          }
        }
      }
    }
    val (res, newctr, newmodel) = invalidateDisjRecr(inputCtr)
    (res, newctr, newmodel, disjsSolvedInIter, callsInPaths)
  }

  def solveWithCegis(tempIds: Set[Identifier], expr: Expr, precond: Expr, initModel: Option[Map[Identifier, Expr]])
  	: (Option[Boolean], Expr, Map[Identifier, Expr]) = {

    val cegisSolver = new CegisCore(context, program, timeout, this)
    val (res, ctr, model) = cegisSolver.solve(tempIds, expr, precond, solveAsInt = false, initModel)
    if (!res.isDefined)
      reporter.info("cegis timed-out on the disjunct...")
    (res, ctr, model)
  }

  def solveNLConstraints(nlctrs: Expr): (Option[Boolean], Map[Identifier, Expr]) = {
    val innerSolver = if (solveAsBitvectors) {
      new UIFZ3Solver(context, program, useBitvectors = true, bitvecSize = bvsize)
    } else {
      new UIFZ3Solver(context, program)
    }
    val solver = SimpleSolverAPI(new TimeoutSolverFactory(SolverFactory(() => innerSolver), timeout * 1000))

    if (this.dumpNLCtrsAsSMTLIB) {
      val filename = program.mainObject.id + "-nlctr" + FileCountGUID.getID + ".smt2"
      if (InvariantUtil.atomNum(nlctrs) >= 5) {
        if (solveAsBitvectors)
          InvariantUtil.toZ3SMTLIB(nlctrs, filename, "QF_BV", context, program, useBitvectors = true, bitvecSize = bvsize)
        else
          InvariantUtil.toZ3SMTLIB(nlctrs, filename, "QF_NRA", context, program)
        println("NLctrs dumped to: " + filename)
      }
    }
    println("solving...")
    val t1 = System.currentTimeMillis()
    val (res, model) = solver.solveSAT(nlctrs)
    val t2 = System.currentTimeMillis()
    println((if (res.isDefined) "solved" else "timed out") + "... in " + (t2 - t1) / 1000.0 + "s")
    Stats.updateCounterTime((t2 - t1), "NL-solving-time", "disjuncts")
    (res, model)
  }

  /**
   * Returns the counter example disjunct
   */
  def getUNSATConstraints(fd: FunDef, inModel: Map[Identifier, Expr], disableCounterExs: Expr): ((Expr, Set[Call]), Expr) = {
    
    val tempVarMap: Map[Expr, Expr] = inModel.map((elem) => (elem._1.toVariable, elem._2)).toMap
    val innerSolver = if(this.useIncrementalSolvingForVCs) vcSolvers(fd)
    			 else new UIFZ3Solver(context, program)
    val instExpr = if (this.useIncrementalSolvingForVCs) {
      val instParamPart = TemplateInstantiator.instantiate(this.paramParts(fd), tempVarMap)      
      val simpPart = simplifyArithmetic(instParamPart)      
      And(simpPart, disableCounterExs)
    } else {
      val instVC = simplifyArithmetic(TemplateInstantiator.instantiate(funcVCs(fd), tempVarMap))
      And(instVC,disableCounterExs)
    }                    
    //For debugging
    if (this.dumpInstantiatedVC) {      
      val wr = new PrintWriter(new File("formula-dump.txt"))
      val fullExpr = if(this.useIncrementalSolvingForVCs) {
        And(innerSolver.getAssertions,instExpr)
      } else 
        instExpr
      println("Instantiated VC of " + fd.id + " is: " + fullExpr)
      wr.println("Function name: " + fd.id)
      wr.println("Formula expr: ")
      ExpressionTransformer.PrintWithIndentation(wr, fullExpr)
      wr.flush()
      wr.close()
    }
    //throw an exception if the candidate expression has reals
    if (InvariantUtil.hasReals(instExpr))
      throw IllegalStateException("Instantiated VC of " + fd.id + " contains reals: " + instExpr)

    reporter.info("checking VC inst ...")
    var t1 = System.currentTimeMillis()
    val (res, model) = if (this.useIncrementalSolvingForVCs) {
      innerSolver.push
      innerSolver.assertCnstr(instExpr)
      val solRes = innerSolver.check
      innerSolver.pop()
      solRes match {
        case Some(true) => (solRes, innerSolver.getModel)
        case _ => (solRes, Map[Identifier,Expr]())
      }
    } else {
      val solver = SimpleSolverAPI(SolverFactory(() => innerSolver))
      solver.solveSAT(instExpr)
    }    
    val vccTime = (System.currentTimeMillis() -t1)
    reporter.info("checked VC inst... in " + vccTime / 1000.0 + "s")
    Stats.updateCounterTime(vccTime, "VC-check-time", "disjuncts")
    Stats.updateCumTime(vccTime, "TotalVCCTime")

    //for debugging
    if (this.trackUnpackedVCCTime) {      
      val upVCinst = simplifyArithmetic(TemplateInstantiator.instantiate(ctrTracker.getVC(fd).unpackedExpr, tempVarMap))
      Stats.updateCounterStats(InvariantUtil.atomNum(upVCinst), "UP-VC-size", "disjuncts")
      
      t1 = System.currentTimeMillis()
      val (res2, _) = SimpleSolverAPI(SolverFactory(() => new UIFZ3Solver(context, program))).solveSAT(upVCinst)
      val unpackedTime = System.currentTimeMillis() - t1
      if(res != res2) {
        throw IllegalStateException("Unpacked VC produces different result: "+upVCinst)
      }
      Stats.updateCumTime(unpackedTime, "TotalUPVCCTime")
      reporter.info("checked UP-VC inst... in " + unpackedTime / 1000.0 + "s")
    }

    t1 = System.currentTimeMillis()
    res match {
      case None => {
        throw IllegalStateException("cannot check the satisfiability of " + funcVCs(fd))
      }
      case Some(false) => {
        //do not generate any constraints
        ((fls, Set()), tru)
      }
      case Some(true) => {
        //For debugging purposes.
        println("Function: " + fd.id + "--Found candidate invariant is not a real invariant! ")
        if (this.printCounterExample) {
          println("Model: " + model)
        }

        //get the disjuncts that are satisfied
        val (data, newctr) = generateCtrsFromDisjunct(fd, model)
        if (newctr == tru)
          throw IllegalStateException("Cannot find a counter-example path!!")

        val t2 = System.currentTimeMillis()
        Stats.updateCounterTime((t2 - t1), "Disj-choosing-time", "disjuncts")
        Stats.updateCumTime((t2 - t1), "Total-Choose-Time")

        (data, newctr)
      }
    }
  }

  /**
   * Returns a disjunct and a set of non linear constraints whose solution will invalidate the disjunct.
   * This is parametrized by two closure
   * (a) a child selector function that decides which children to consider.
   * (b) a doesAlias function that decides which function / ADT constructor calls to consider.
   */
  val evaluator = new DefaultEvaluator(context, program) //as of now used only for debugging
  //a helper method 
  def doesSatisfyModel(expr: Expr, model: Map[Identifier, Expr]): Boolean = {
    evaluator.eval(expr, model).result match {
      case Some(BooleanLiteral(true)) => true
      case _ => false
    }
  }

  private def generateCtrsFromDisjunct(fd: FunDef, model: Map[Identifier, Expr]): ((Expr, Set[Call]), Expr) = {

    val formula = ctrTracker.getVC(fd)
    //this picks the satisfiable disjunct of the VC modulo axioms
    val satCtrs = formula.pickSatDisjunct(formula.firstRoot, model)
    //for debugging        
    if (this.debugChooseDisjunct || this.printPathToConsole || this.dumpPathAsSMTLIB) {
      val pathctrs = satCtrs.map(_.toExpr)
      val plainFormula = And(pathctrs)
      val pathcond = simplifyArithmetic(plainFormula)

      if (this.debugChooseDisjunct) {
        satCtrs.filter(_.isInstanceOf[LinearConstraint]).map(_.toExpr).foreach((ctr) => {
          if (!doesSatisfyModel(ctr, model))
            throw IllegalStateException("Path ctr not satisfied by model: " + ctr)
        })
      }

      if (this.verifyInvariant) {
        println("checking invariant for path...")
        InvariantUtil.checkInvariant(pathcond, context, program)
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
        InvariantUtil.toZ3SMTLIB(pathcond, filename, "QF_NIA", context, program)
        println("Path dumped to: " + filename)
      }
    }

    var calls = Set[Call]()
    var cons = Set[Expr]()
    satCtrs.foreach(ctr => ctr match {
      case t: Call => calls += t
      case t: ADTConstraint if (t.cons.isDefined) => cons += t.cons.get
      case _ => ;
    })
    val callExprs = calls.map(_.toExpr)

    //reporter.info("choosing axioms...")
    var t1 = System.currentTimeMillis()
    val axiomCtrs = ctrTracker.specInstantiator.axiomsForCalls(formula, calls, model)
    var t2 = System.currentTimeMillis()
    //reporter.info("chosen axioms...in " + (t2 - t1) / 1000.0 + "s")
    Stats.updateCumTime((t2 - t1), "Total-AxiomChoose-Time")

    //for stats
    //reporter.info("starting UF/ADT elimination...")
    t1 = System.currentTimeMillis()
    val callCtrs = (new UFADTEliminator(context, program)).constraintsForCalls((callExprs ++ cons), model).map(ConstraintUtil.createConstriant _)
    t2 = System.currentTimeMillis()
    //reporter.info("completed UF/ADT elimination...in " + (t2 - t1) / 1000.0 + "s")
    Stats.updateCumTime((t2 - t1), "Total-ElimUF-Time")

    //exclude guards, separate calls and cons from the rest
    var lnctrs = Set[LinearConstraint]()
    var temps = Set[LinearTemplate]()
    (satCtrs ++ callCtrs ++ axiomCtrs).foreach(ctr => ctr match {
      case t: LinearConstraint => lnctrs += t
      case t: LinearTemplate => temps += t
      case _ => ;
    })

    if (this.debugChooseDisjunct) {
      lnctrs.map(_.toExpr).foreach((ctr) => {
        if (!doesSatisfyModel(ctr, model))
          throw IllegalStateException("Ctr not satisfied by model: " + ctr)
      })
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
      (And(lnctrs.map(_.toExpr)), fls)
    } else {
      
      if (this.debugElimination) {
        //println("Path Constraints (before elim): "+(lnctrs ++ temps))
        if (this.verifyInvariant) {
          println("checking invariant for disjunct before elimination...")
          InvariantUtil.checkInvariant(And((lnctrs ++ temps).map(_.template)), context, program)
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
          val debugRes = InvariantUtil.checkInvariant(And((ctrs ++ temps).map(_.template)), context, program)
        })
      } else None
      val elimLnctrs = LinearConstraintUtil.apply1PRuleOnDisjunct(lnctrs, elimVars, debugger)
      val t2 = System.currentTimeMillis()
            
      if (this.debugElimination) {        
        println("Path constriants (after elimination): " + elimLnctrs)
        if (this.verifyInvariant) {
          println("checking invariant for disjunct after elimination...")
          InvariantUtil.checkInvariant(And((elimLnctrs ++ temps).map(_.template)), context, program)
        }
      }
      //for stats
      if (InferInvariantsPhase.dumpStats) {
        var elimCtrCount = 0
        var elimCtrs = Seq[LinearConstraint]()
        var elimRems = Set[Identifier]()
        elimLnctrs.foreach((lc) => {
          val evars = variablesOf(lc.toExpr).intersect(elimVars)
          if (!evars.isEmpty) {
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
      
      //TODO: simplify the formulas and remove implied conjuncts if possible (note the formula is satisfiable, so there can be no inconsistencies) 
      //e.g, remove: a <= b if we have a = b or if a < b
      //Also, enrich the rules for quantifier elimination: try z3 quantifier elimination on variables that have an equality. 
      
      //TODO: Use the dependence chains in the formulas to identify what to assertionize 
      // and what can never be implied by solving for the templates                       
      
      val disjunct = And((newLnctrs ++ temps).map(_.template))
      val implCtrs = farkasSolver.constraintsForUnsat(newLnctrs, temps)

      //for debugging
      if (this.debugReducedFormula) {
        println("Final Path Constraints: " + disjunct)
        if (this.verifyInvariant) {
          println("checking invariant for final disjunct... ")
          InvariantUtil.checkInvariant(disjunct, context, program)
        }
      }

      (disjunct, implCtrs)
    }
  }

}
