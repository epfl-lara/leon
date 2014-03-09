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

class NLTemplateSolver(context: LeonContext,
  program: Program,
  rootFun: FunDef,
  ctrTracker: ConstraintTracker,
  tempFactory: TemplateFactory,
  timeout: Int,
  tightBounds: Boolean) extends TemplateSolver(context, program, rootFun, ctrTracker, tempFactory, timeout) {

  private val farkasSolver = new FarkasLemmaSolver()
  private val minimizer = new Minimizer(context, program, timeout)

  val disableCegis = true
  val solveAsBitvectors = false
  val bvsize = 5

  //flags controlling debugging
  //TODO: there is serious bug in using incremental solving. Report this to z3 community
  val debugIncremental = false
  val debugElimination = false
  val debugChooseDisjunct = false
  val debugAxioms = false
  val verifyInvariant = false
  val debugReducedFormula = false

  //print flags
  val printCounterExample = false
  val printPathToConsole = false
  val dumpPathAsSMTLIB = false
  val dumpNLCtrsAsSMTLIB = false
  val printCallConstriants = false
  val printReducedFormula = false
  val dumpInstantiatedVC = false

  /**
   * This function computes invariants belonging to the given templates incrementally.
   * The result is a mapping from function definitions to the corresponding invariants.
   */
  override def solve(tempIds: Set[Identifier], funcVCs: Map[FunDef, Expr]): (Option[Map[FunDef, Expr]], Option[Set[Call]]) = {

    /*For debugging:
     * here we can plug-in the desired invariant and check if it falsifies 
     * the verification condition      
     * */
    /*var tempMap = Map[Expr,Expr]()
    funcVCs.foreach((pair)=> {
      val (fd, vc)=pair      
      if(fd.id.name.contains("size")) {
        variablesOf(vc).foreach((id) => 
          if(TemplateIdFactory.IsTemplateIdentifier(id) && id.name.contains("d"))
            tempMap += (id.toVariable -> RealLiteral(0,1))
          )          
      }
      else if(fd.id.name.contains("nnf")) {
        variablesOf(vc).foreach((id) => 
          if(TemplateIdFactory.IsTemplateIdentifier(id)){
            if(id.name == "a?") tempMap += (id.toVariable -> RealLiteral(2,1))
            if(id.name == "b?") tempMap += (id.toVariable -> RealLiteral(-1,1))
          })
      }
    })
    funcVCs.keys.foreach((fd) => {
      val ivc = simplifyArithmetic(TemplateInstantiator.instantiate(funcVCs(fd), tempMap))
      val tsolver = new UIFZ3Solver(context, program, autoComplete = false)
      tsolver.assertCnstr(ivc)
      if (!(tsolver.check == Some(false))) {
        println("verification condition is not inductive for: " + fd.id)
        val (dis, _) = getNLConstraints(fd, ivc, tempMap)
        val disj = simplifyArithmetic(dis)
        println("disjunct: " + disj)
        println("inst-disjunct: " + simplifyArithmetic(TemplateInstantiator.instantiate(disj, tempMap)))      
        System.console.readLine()
      }      
      tsolver.free()
    })*/
    val solverWithCtr = new UIFZ3Solver(this.context, program)
    solverWithCtr.assertCnstr(tru)

    val initModel = {
      val simplestModel = tempIds.map((id) => (id -> simplestValue(id.toVariable))).toMap
      simplestModel
    }
    val sol = recSolve(initModel, funcVCs, tru, Seq(), solverWithCtr, Set())

    solverWithCtr.free()

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

  //TODO: this code is very ugly, fix this asap
  def recSolve(model: Map[Identifier, Expr],
    funcVCs: Map[FunDef, Expr],
    inputCtr: Expr,
    solvedDisjs: Seq[Expr],
    //cegisIncrSolver : CegisIncrSolver,
    solverWithCtr: UIFZ3Solver,
    seenCalls: Set[Call]): (Option[Map[FunDef, Expr]], Option[Set[Call]]) = {

    //Information: printing the candidate invariants found at this step
    println("candidate Invariants")
    val candInvs = getAllInvariants(model)
    candInvs.foreach((entry) => println(entry._1.id + "-->" + entry._2))

    val funcs = funcVCs.keys
    val tempIds = model.keys
    val tempVarMap: Map[Expr, Expr] = model.map((elem) => (elem._1.toVariable, elem._2)).toMap
    val inputSize = InvariantUtil.atomNum(inputCtr)

    var disjsSolvedInIter = Seq[Expr]()
    var conflictingFuns = funcs.toSet
    //mapping from the functions to the counter-example paths that were seen
    var seenPaths = MutableMap[FunDef, Seq[Expr]]()
    def updateSeenPaths(fd: FunDef, cePath: Expr): Unit = {
      if (seenPaths.contains(fd)) {
        seenPaths.update(fd, cePath +: seenPaths(fd))
      } else {
        seenPaths += (fd -> Seq(cePath))
      }
    }

    //TODO: There is a serious bug in z3 in incremental solving. The following code is for reproducing the bug            
    if (this.debugIncremental) {
      solverWithCtr.assertCnstr(inputCtr)
    }

    var callsInPaths = Set[Call]()
    def disableADisjunct(prevCtr: Expr): (Option[Boolean], Expr, Map[Identifier, Expr]) = {

      Stats.updateCounter(1, "disjuncts")

      var blockedCEs = false
      var confFunctions = Set[FunDef]()
      var confDisjuncts = Seq[Expr]()

      val newctrs = conflictingFuns.foldLeft(Seq[Expr]())((acc, fd) => {

        val instVC = simplifyArithmetic(TemplateInstantiator.instantiate(funcVCs(fd), tempVarMap))
        //here, block the counter-examples seen thus far for the function
        val disableCounterExs = if (seenPaths.contains(fd)) {
          blockedCEs = true
          Not(Or(seenPaths(fd)))
        } else tru
        val instVCmodCE = And(instVC, disableCounterExs)
        val (data, ctrsForFun) = getNLConstraints(fd, instVCmodCE, tempVarMap)
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

        if (this.debugIncremental)
          solverWithCtr.assertCnstr(newPart)

        //here we need to solve for the newctrs + inputCtrs
        val combCtr = And(prevCtr, newPart)
        val innerSolver = if (solveAsBitvectors) {
          new UIFZ3Solver(context, program, useBitvectors = true, bitvecSize = bvsize)
        } else {
          new UIFZ3Solver(context, program)
        }
        val solver = SimpleSolverAPI(new TimeoutSolverFactory(SolverFactory(() => innerSolver), timeout * 1000))

        if (this.dumpNLCtrsAsSMTLIB) {
          val filename = program.mainObject.id + "-nlctr" + FileCountGUID.getID + ".smt2"
          if ((newSize + inputSize) >= 5) {
            if (solveAsBitvectors)
              InvariantUtil.toZ3SMTLIB(combCtr, filename, "QF_BV", context, program, useBitvectors = true, bitvecSize = bvsize)
            else
              InvariantUtil.toZ3SMTLIB(combCtr, filename, "QF_NRA", context, program)
            println("NLctrs dumped to: " + filename)
          }
        }
        println("solving...")
        val t1 = System.currentTimeMillis()
        val (res, newModel) = solver.solveSAT(combCtr)
        val t2 = System.currentTimeMillis()
        println((if (res.isDefined) "solved" else "timed out") + "... in " + (t2 - t1) / 1000.0 + "s")
        Stats.updateCounterTime((t2 - t1), "NL-solving-time", "disjuncts")

        res match {
          case None => {
            //here we have timed out while solving the non-linear constraints
            if (!this.disableCegis)
              reporter.info("NLsolver timed-out on the disjunct... starting cegis phase...")
            else
              reporter.info("NLsolver timed-out on the disjunct... blocking this disjunct...")
            //run cegis on all the disjuncts collected thus far.            
            //This phase can only look for sat. It cannot prove unsat
            /*val (cgRes, _, cgModel) =  cegisIncrSolver.solveInSteps(tempIds.toSet, Or(solvedDisjs ++ confDisjuncts))
            cgRes match {
              //cegis found a model ??
              case Some(true) => {
                //note we have the cegisCtr stored in the 'cegisIncr' solver
                (Some(true), inputCtr, cgModel)
              }                            
              //cegis timed out?? note that 'cgRes' can never be false. 
              case _ => {
                reporter.info("Plain cegis timed-out on the disjunct... starting combined phase...")*/

            if (!this.disableCegis) {
              val cegisSolver = new CegisCore(context, program, timeout, this)
              val (cegisRes2, cegisCtr2, cegisModel2) = cegisSolver.solve(tempIds.toSet, Or(confDisjuncts), inputCtr,
                solveAsInt = false, initModel = Some(model))
              cegisRes2 match {
                //found a model ??
                case Some(true) => {
                  disjsSolvedInIter ++= confDisjuncts
                  (Some(true), And(inputCtr, cegisCtr2), cegisModel2)
                }
                //there exists no model ??
                case Some(false) => {
                  disjsSolvedInIter ++= confDisjuncts
                  //here also return the calls that needs to be unrolled
                  (None, fls, Map())
                }
                //timed out??
                case _ => {
                  reporter.info("cegis timed-out on the disjunct... retrying...")
                  Stats.updateCumStats(1, "retries")

                  //disable this disjunct and retry but, use the inputCtrs + the constraints generated by cegis from the next iteration
                  disableADisjunct(And(inputCtr, cegisCtr2))
                }
              }
            } else {
              Stats.updateCumStats(1, "retries")
              disableADisjunct(inputCtr)
            }
            //} 
            //}
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
            if (debugIncremental) {
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

            disjsSolvedInIter ++= confDisjuncts
            //new model may not have mappings for all the template variables, hence, use the mappings from earlier models            
            val compModel = tempIds.map((id) => {
              if (newModel.contains(id))
                (id -> newModel(id))
              else
                (id -> model(id))
            }).toMap

            //println("New model: "+ newModel + " Completed Model: "+compModel)
            (Some(true), combCtr, compModel)
          }
        }
      }
    }

    val (res, newCtr, newModel) = disableADisjunct(inputCtr)
    res match {
      case None => {
        //here, we cannot proceed and have to return unknown
        //However, we can return the calls that need to be unrolled                       
        (None, Some(seenCalls ++ callsInPaths))
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
          } 
          else {
            val minModel = minimizer.tightenTimeBounds(template.get, inputCtr, model)
            minimized = true
            if (minModel == model){
              minimizationCompleted
              (Some(getAllInvariants(model)), None)
            }
            else {
              recSolve(minModel, funcVCs, inputCtr, solvedDisjs, solverWithCtr, seenCalls)
            }
          }          
//          val minVarMap: Map[Expr, Expr] = minModel.map((elem) => (elem._1.toVariable, elem._2)).toMap
//          else {
//            val isInv = funcVCs.keys.forall((fd) => {
//              val instVC = simplifyArithmetic(TemplateInstantiator.instantiate(funcVCs(fd), minVarMap))
//              val solver = SimpleSolverAPI(SolverFactory(() => new UIFZ3Solver(context, program)))
//              val (res, _) = solver.solveSAT(instVC)
//              res match {
//                case Some(false) => true
//                case _ => false
//              }
//            })
//            if (isInv) {
//              minStarted = false
//              val mintime = (System.currentTimeMillis() - minStartTime)
//              Stats.updateCounterTime(mintime, "minimization-time", "procs")
//              Stats.updateCumTime(mintime, "Total-Min-Time")
//
//              (Some(getAllInvariants(minModel)), None)
//            } else
//              recSolve(minModel, funcVCs, inputCtr, solvedDisjs, solverWithCtr, seenCalls)
//          }
        } else {
          (Some(getAllInvariants(model)), None)
        }
      }
      case Some(true) => {
        //here, we have found a new candidate invariant. Hence, the above process needs to be repeated
        minimized = false
        recSolve(newModel, funcVCs, newCtr, solvedDisjs ++ disjsSolvedInIter, solverWithCtr, seenCalls ++ callsInPaths)
      }
    }
  }

  /**
   * Returns the counter example disjunct
   */
  def getNLConstraints(fd: FunDef, instVC: Expr, tempVarMap: Map[Expr, Expr]): ((Expr, Set[Call]), Expr) = {
    //For debugging
    if (this.dumpInstantiatedVC) {
      val wr = new PrintWriter(new File("formula-dump.txt"))
      println("Instantiated VC of " + fd.id + " is: " + instVC)
      wr.println("Function name: " + fd.id)
      wr.println("Formula expr: ")
      ExpressionTransformer.PrintWithIndentation(wr, instVC)
      wr.flush()
      wr.close()
    }

    //throw an exception if the candidate expression has reals
    if (InvariantUtil.hasReals(instVC))
      throw IllegalStateException("Instantiated VC of " + fd.id + " contains reals: " + instVC)

    val solver = SimpleSolverAPI(SolverFactory(() => new UIFZ3Solver(context, program)))

    reporter.info("checking VC inst ...")
    var t1 = System.currentTimeMillis()
    //val res = solEval.check
    val (res, model) = solver.solveSAT(instVC)
    val t2 = System.currentTimeMillis()
    //reporter.info("checked VC inst... in " + (t2 - t1) / 1000.0 + "s")
    Stats.updateCounterTime((t2 - t1), "VC-check-time", "disjuncts")

    t1 = System.currentTimeMillis()
    res match {
      case None => {
        throw IllegalStateException("cannot check the satisfiability of " + instVC)
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

    val satCtrs = pickSatDisjunct(rootGuards(fd), model)
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
    val axiomCtrs = axiomsForPath(callExprs, model)
    var t2 = System.currentTimeMillis()
    //reporter.info("chosen axioms...in " + (t2 - t1) / 1000.0 + "s")
    Stats.updateCumTime((t2 - t1), "Total-AxiomChoose-Time")

    //for stats
    //reporter.info("starting UF/ADT elimination...")
    t1 = System.currentTimeMillis()
    val callCtrs = constraintsForCalls((callExprs ++ cons), model).map(ConstraintUtil.createConstriant _)
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

      //TODO: try some optimizations here to reduce the number of constraints to be considered
      // Note: we can use the interpolation property of arithmetics        

      //compute variables to be eliminated
      val ctrVars = lnctrs.foldLeft(Set[Identifier]())((acc, lc) => acc ++ variablesOf(lc.toExpr))
      val tempVars = temps.foldLeft(Set[Identifier]())((acc, lt) => acc ++ variablesOf(lt.template))
      val elimVars = ctrVars.diff(tempVars)

      //For debugging
      /*if (debugElimination) {
          reporter.info("Number of linear constraints: " + lnctrs.size)
          reporter.info("Number of template constraints: " + temps.size)
          reporter.info("Number of elimVars: " + elimVars.size)
        } */

      val debugger = if (debugElimination && verifyInvariant) {
        Some((ctrs: Seq[LinearConstraint]) => {
          //println("checking disjunct before elimination...")
          //println("ctrs: "+ctrs)
          val debugRes = InvariantUtil.checkInvariant(And((ctrs ++ temps).map(_.template)), context, program)
        })
      } else None
      val elimLnctrs = LinearConstraintUtil.apply1PRuleOnDisjunct(lnctrs, elimVars, debugger)

      //for stats
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
      if (this.debugElimination) {
        /*reporter.info("Number of linear constraints (after elim): " + elimLnctrs.size)          
          reporter.info("Number of constraints with elimVars: " + elimCtrCount)
          reporter.info("constraints with elimVars: " + elimCtrs)
          reporter.info("Number of remaining elimVars: " + elimRems.size)*/
        //println("Elim vars: "+elimVars)
        println("Path constriants (after elimination): " + elimLnctrs)
        if (this.verifyInvariant) {
          println("checking invariant for disjunct after elimination...")
          InvariantUtil.checkInvariant(And((elimLnctrs ++ temps).map(_.template)), context, program)
        }

      }
      //for stats
      if (InferInvariantsPhase.dumpStats) {
        Stats.updateCounterStats((elimVars.size - elimRems.size), "Eliminated-Vars", "disjuncts")
        Stats.updateCounterStats((lnctrs.size - elimLnctrs.size), "Eliminated-Atoms", "disjuncts")
        Stats.updateCounterStats(temps.size, "Param-Atoms", "disjuncts")
        Stats.updateCounterStats(lnctrs.size, "NonParam-Atoms", "disjuncts")
      }
      val newLnctrs = elimLnctrs.toSet.toSeq

      //TODO: one idea: use the dependence chains in the formulas to identify what to assertionize 
      // and what can never be implied by solving for the templates                       
      //TODO: are we checking enough ? Can we eliminate more ?
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

  /**
   * Convert the theory formula into linear arithmetic formula.
   * The calls could be functions calls or ADT constructor calls.
   * The parameter 'doesAliasInCE' is an abbreviation for 'Does Alias in Counter Example'
   */
  //TODO: important: optimize this code it seems to take a lot of time    
  val makeEfficient = true //this will happen at the expense of completeness  
  def constraintsForCalls(calls: Set[Expr], model: Map[Identifier, Expr]): Seq[Expr] = {

    var eqGraph = new UndirectedGraph[Expr]() //an equality graph
    var neqSet = Set[(Expr, Expr)]()

    //compute the cartesian product of the calls and select the pairs having the same function symbol and also implied by the precond
    val vec = calls.toArray
    val size = calls.size
    var j = 0
    val product = vec.foldLeft(Set[(Expr, Expr)]())((acc, call) => {

      //an optimization: here we can exclude calls to maxFun from axiomatization, they will be inlined anyway
      /*val shouldConsider = if(InvariantUtil.isCallExpr(call)) {
        val BinaryOperator(_,FunctionInvocation(calledFun,_), _) = call
        if(calledFun == DepthInstPhase.maxFun) false
        else true               
      } else true*/
      var pairs = Set[(Expr, Expr)]()
      for (i <- j + 1 until size) {
        val call2 = vec(i)
        if (mayAlias(call, call2)) {
          pairs ++= Set((call, call2))
        }
      }
      j += 1
      acc ++ pairs
    })
    reporter.info("Number of compatible calls: " + product.size)
    Stats.updateCounterStats(product.size, "Compatible-Calls", "disjuncts")

    //check if two calls (to functions or ADT cons) have the same value in the model 
    def doesAlias(call1: Expr, call2: Expr): Boolean = {
      val BinaryOperator(Variable(r1), _, _) = call1
      val BinaryOperator(Variable(r2), _, _) = call2
      val resEquals = (model(r1) == model(r2))
      if (resEquals) {
        if (InvariantUtil.isCallExpr(call1)) {
          val (ants, _) = axiomatizeCalls(call1, call2)
          val antsHold = ants.forall(ant => {
            val BinaryOperator(Variable(lid), Variable(rid), _) = ant
            (model(lid) == model(rid))
          })
          antsHold
        } else true
      } else false
    }

    def predForEquality(call1: Expr, call2: Expr): Seq[Expr] = {

      val eqs = if (InvariantUtil.isCallExpr(call1)) {        
        val (_, rhs) = axiomatizeCalls(call1, call2)
        Seq(rhs)
      } else {
        val (lhs, rhs) = axiomatizeADTCons(call1, call2)
        lhs :+ rhs
      }
      //remove self equalities. 
      val preds = eqs.filter(_ match {
        case BinaryOperator(Variable(lid), Variable(rid), _) => {
          if (lid == rid) false
          else {
            if (lid.getType == Int32Type || lid.getType == RealType) true
            else false
          }
        }
        case e @ _ => throw new IllegalStateException("Not an equality or Iff: " + e)
      })
      preds
    }

    //TODO: This has an incomplete way of handling ADTs for efficiency. Can this be fixed ?
    def predForDisequality(call1: Expr, call2: Expr): Seq[Expr] = {
      
      val (ants, _) = if (InvariantUtil.isCallExpr(call1)) {
        axiomatizeCalls(call1, call2)
      } else {
        axiomatizeADTCons(call1, call2)
      }

      if (makeEfficient && ants.exists(_ match {
        case Equals(l, r) if (l.getType != Int32Type && l.getType != RealType && l.getType != BooleanType) => true
        case _ => false
      })) {
        Seq()
      } else {
        var unsatIntEq: Option[Expr] = None
        var unsatOtherEq: Option[Expr] = None
        ants.foreach(eq =>
          if (!unsatOtherEq.isDefined) {
            eq match {
              case Equals(lhs @ Variable(_), rhs @ Variable(_)) if (model(lhs.id) != model(rhs.id)) => {
                if (lhs.getType != Int32Type && lhs.getType != RealType)
                  unsatOtherEq = Some(eq)
                else if (!unsatIntEq.isDefined)
                  unsatIntEq = Some(eq)
              }
              case Iff(lhs @ Variable(_), rhs @ Variable(_)) if (model(lhs.id) != model(rhs.id)) =>
                unsatOtherEq = Some(eq)
              case _ => ;
            }
          })
        if (unsatOtherEq.isDefined) Seq() //need not add any constraint
        else if (unsatIntEq.isDefined) {
          //pick the constraint a < b or a > b that is satisfied
          val Equals(lhs @ Variable(lid), rhs @ Variable(rid)) = unsatIntEq.get
          val IntLiteral(lval) = model(lid)
          val IntLiteral(rval) = model(rid)
          val atom = if (lval < rval) LessThan(lhs, rhs)
          else if (lval > rval) GreaterThan(lhs, rhs)
          else throw IllegalStateException("Models are equal!!")

          /*if (ants.exists(_ match {
              case Equals(l, r) if (l.getType != Int32Type && l.getType != RealType && l.getType != BooleanType) => true
              case _ => false
            })) {
              Stats.updateCumStats(1, "Diseq-blowup")
            }*/
          Seq(atom)
        } else throw IllegalStateException("All arguments are equal: " + call1 + " in " + model)
      }
    }
    
    val newctrs = product.foldLeft(Seq[Expr]())((acc, pair) => {
      val (call1, call2) = (pair._1, pair._2)
      //println("Assertionizing "+call1+" , call2: "+call2)      
      if (!eqGraph.BFSReach(call1, call2) && !neqSet.contains((call1, call2)) && !neqSet.contains((call2, call1))) {
        if (doesAlias(call1, call2)) {
          eqGraph.addEdge(call1, call2)
          //note: here it suffices to check for adjacency and not reachability of calls (i.e, exprs).
          //This is because the transitive equalities (corresponding to rechability) are encoded by the generated equalities.
          acc ++ predForEquality(call1, call2)

        } /*else if(this.callsWithAxioms.contains(call1)) {
    	    //is this complete? 
    	     * acc
    	     * }*/ 
        else {
          neqSet ++= Set((call1, call2))
          acc ++ predForDisequality(call1, call2)
        }
      } else acc
    })
    
    reporter.info("Number of equal calls: " + eqGraph.getEdgeCount)
    newctrs
  }

  def axiomsForPath(calls: Set[Expr], model: Map[Identifier, Expr]): Seq[Constraint] = {
    //using the axiom roots for now
    //TODO: is there a better way to implement this 
    val vec = calls.toArray
    val size = calls.size
    var j = 0
    vec.foldLeft(Seq[Constraint]())((acc, call1) => {
      var satDisj = Set[Constraint]()
      for (i <- j + 1 until size) {
        val call2 = vec(i)
        val axRoot = axiomRoots.get((call1, call2))
        if (axRoot.isDefined)
          satDisj ++= pickSatDisjunct(axRoot.get, model)
      }
      j += 1
      acc ++ satDisj
    })
  }

  /**
   * This function actually checks if two non-primitive expressions could have the same value
   * (when some constraints on their arguments hold).
   * Remark: notice  that when the expressions have ADT types, then this is basically a form of may-alias check.
   */
  def mayAlias(e1: Expr, e2: Expr): Boolean = {
    //check if call and call2 are compatible
    (e1, e2) match {
      case (Equals(_, FunctionInvocation(fd1, _)), Equals(_, FunctionInvocation(fd2, _))) if (fd1.id == fd2.id) => true
      case (Iff(_, FunctionInvocation(fd1, _)), Iff(_, FunctionInvocation(fd2, _))) if (fd1.id == fd2.id) => true
      case (Equals(_, CaseClass(cd1, _)), Equals(_, CaseClass(cd2, _))) if (cd1.id == cd2.id) => true
      case (Equals(_, tp1 @ Tuple(e1)), Equals(_, tp2 @ Tuple(e2))) if (tp1.getType == tp2.getType) => true
      case _ => false
    }
  }

  /**
   * This procedure generates constraints for the calls to be equal
   */
  def axiomatizeCalls(call1: Expr, call2: Expr): (Seq[Expr], Expr) = {

    val (v1, fi1, v2, fi2) = if (call1.isInstanceOf[Equals]) {
      val Equals(r1, f1 @ FunctionInvocation(_, _)) = call1
      val Equals(r2, f2 @ FunctionInvocation(_, _)) = call2
      (r1, f1, r2, f2)
    } else {
      val Iff(r1, f1 @ FunctionInvocation(_, _)) = call1
      val Iff(r2, f2 @ FunctionInvocation(_, _)) = call2
      (r1, f1, r2, f2)
    }

    val ants = (fi1.args.zip(fi2.args)).foldLeft(Seq[Expr]())((acc, pair) => {
      val (arg1, arg2) = pair
      acc :+ Equals(arg1, arg2)
    })
    val conseq = Equals(v1, v2)
    (ants, conseq)
  }

  /**
   * The returned pairs should be interpreted as a bidirectional implication
   */
  def axiomatizeADTCons(sel1: Expr, sel2: Expr): (Seq[Expr], Expr) = {

    val (v1, args1, v2, args2) = sel1 match {
      case Equals(r1 @ Variable(_), CaseClass(_, a1)) => {
        val Equals(r2 @ Variable(_), CaseClass(_, a2)) = sel2
        (r1, a1, r2, a2)
      }
      case Equals(r1 @ Variable(_), Tuple(a1)) => {
        val Equals(r2 @ Variable(_), Tuple(a2)) = sel2
        (r1, a1, r2, a2)
      }
    }

    val ants = (args1.zip(args2)).foldLeft(Seq[Expr]())((acc, pair) => {
      val (arg1, arg2) = pair
      acc :+ Equals(arg1, arg2)
    })
    val conseq = Equals(v1, v2)
    (ants, conseq)
  }
}
