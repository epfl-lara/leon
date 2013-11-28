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

class NLTemplateSolver(context : LeonContext, 
    program : Program,
    ctrTracker : ConstraintTracker, 
    tempFactory: TemplateFactory,    
    timeout: Int) extends TemplateSolver(context, program, ctrTracker, tempFactory, timeout) {
  
  private val farkasSolver = new FarkasLemmaSolver()  
  
  //flags controlling debugging and statistics generation
  //TODO: there is serious bug in using incremental solving. Report this to z3 community
  val debugIncremental = false  
  val debugElimination = false
  val printPathToConsole = false
  val dumpPathAsSMTLIB = false
  val printCallConstriants = false
  val printReducedFormula = false  
  val dumpNLFormula = false
  val dumpInstantiatedVC = false 
  val debugAxioms = false      

  /**
   * This function computes invariants belonging to the given templates incrementally.
   * The result is a mapping from function definitions to the corresponding invariants.
   */  
  override def solve(tempIds : Set[Identifier], funcVCs: Map[FunDef, Expr]) : Option[Map[FunDef, Expr]] = {
    
    val solverWithCtr = new UIFZ3Solver(this.context, program)
    solverWithCtr.assertCnstr(tru)
    
    val simplestModel = tempIds.map((id) => (id -> simplestValue(id.toVariable))).toMap    
    val sol = recSolve(simplestModel, funcVCs, tru, solverWithCtr)
    
    solverWithCtr.free()
    sol
  }
   
  def recSolve(model : Map[Identifier, Expr],
      funcVCs: Map[FunDef, Expr],
      inputCtr : Expr, 
      solverWithCtr: UIFZ3Solver) 
  	: Option[Map[FunDef, Expr]] = {    
    
    //for stats
    Stats.innerIterations += 1
    //the following does not seem to be necessary as z3 updates the model on demand
    //val compModel = completeModel(model, TemplateIdFactory.getTemplateIds)
    
    //For debugging: printing the candidate invariants found at this step
    println("candidate Invariants")
    val candInvs = getAllInvariants(model)
    candInvs.foreach((entry) => println(entry._1.id + "-->" + entry._2))
    
    val funcs = funcVCs.keys           
    val tempVarMap: Map[Expr, Expr] = model.map((elem) => (elem._1.toVariable, elem._2)).toMap    
    var conflictingFuns = Set[FunDef]()
    //mapping from the functions to the counter-example (in the form expressions) that result in hard NL constraints
    var seenPaths = MutableMap[FunDef,Seq[Expr]]()
    def updateSeenPaths(fd: FunDef, cePath: Expr): Unit = {
      if (seenPaths.contains(fd)) {
        seenPaths.update(fd, cePath +: seenPaths(fd))
      } else {
        seenPaths += (fd -> Seq(cePath))
      }
    }
        
    val initialctrs = funcs.foldLeft(Seq[Expr]())((acc, fd) => {

      val instVC = simplifyArithmetic(TemplateInstantiator.instantiate(funcVCs(fd), tempVarMap))
      //find new non-linear constraints based on models to instVC (which are counter examples)
      val (disjunct, ctrsForFun) = getNLConstraints(fd, instVC, tempVarMap)
      //instantiate path
      val cePath = simplifyArithmetic(TemplateInstantiator.instantiate(disjunct, tempVarMap))
      
      //sanity check
      if (variablesOf(cePath).exists(TemplateIdFactory.IsTemplateIdentifier _))
        throw IllegalStateException("Found template identifier in counter-example disjunct: " + cePath)
      
      if(ctrsForFun != tru) {
        conflictingFuns += fd
        updateSeenPaths(fd, cePath)        
        acc :+ ctrsForFun        
      } else acc    	  
    })

    //have we found a real invariant ?
    if (initialctrs.isEmpty) {
      //yes, hurray
      //print some statistics 
      //reporter.info("- Number of explored paths (of the DAG) in this unroll step: " + exploredPaths)
      Some(getAllInvariants(model))
    } else {
      //For statistics.
      //reporter.info("- Number of new Constraints: " + newctrs.size)          
      //call the procedure recursively
      val initialctr = And(initialctrs)            

      //add the new constraints      
      //TODO: There is a serious bug here, report the bug to z3 if it happens again      
      //For debugging
      if (this.dumpNLFormula) {
        solverWithCtr.assertCnstr(initialctr)
        FileCountGUID.fileCount += 1
        val filename = "z3formula-" + FileCountGUID.fileCount + ".smt"
        val pwr = new PrintWriter(filename)
        pwr.println(solverWithCtr.ctrsToString("QF_NRA"))
        pwr.flush()
        pwr.close()
        println("Formula printed to File: " + filename)
      }                                   

      //solve the new set of non-linear constraints
      def solveNLConstraints(easyPart: Expr, newPart: Expr): (Option[Boolean], Map[Identifier, Expr], Expr) = {
                
        //for stats and debugging               
        val farkasSize =  InvariantUtil.atomNum(newPart) 
        
        if(InferInvariantsPhase.dumpStats) {
          val (cum, max) = Stats.cumMax(Stats.cumFarkaSize, Stats.maxFarkaSize, farkasSize + InvariantUtil.atomNum(easyPart))
          Stats.cumFarkaSize = cum; Stats.maxFarkaSize = max  
        }        
        println("# of atomic predicates: " + farkasSize)
                
        val solver = SimpleSolverAPI(
            new TimeoutSolverFactory(SolverFactory(() => new UIFZ3Solver(context, program)), 
            timeout * 1000))

        println("solving...")
        val t1 = System.currentTimeMillis()
        val (res, newModel) = solver.solveSAT(And(easyPart, newPart))
        val t2 = System.currentTimeMillis()
        if (res.isDefined)
          println("solved... in " + (t2 - t1) / 1000.0 + "s")
        else
          println("timed out... in " + (t2 - t1) / 1000.0 + "s")

        //for stats
        if (InferInvariantsPhase.dumpStats) {
          val (cum2, max2) = Stats.cumMax(Stats.cumFarkaTime, Stats.maxFarkaTime, (t2 - t1))
          Stats.cumFarkaTime = cum2; Stats.maxFarkaTime = max2
        }

        //for debugging
        if (debugIncremental) {
          solverWithCtr.innerCheck
        }
        //important reset res to none if the model we found has denominator as zero
        /*val finalRes = if (res == Some(true)) {
          val denomZero = newModel.values.exists((e: Expr) => e match {
            case RealLiteral(_, 0) => true
            case _ => false
          })
          if (denomZero){
            reporter.info("The model has a divide by zero")
            throw IllegalStateException("")
          } else res
        } else res*/
        res match {
          case None => {
            //here, we might have timed out, so block current counter-example and get a new one
            val newctrs = conflictingFuns.foldLeft(Seq[Expr]())((acc, fd) => {

              val instVC = simplifyArithmetic(TemplateInstantiator.instantiate(funcVCs(fd), tempVarMap))
              val disableCounterExs = Not(Or(seenPaths(fd)))
              val instVCmodCE = And(instVC, disableCounterExs)
              val (disjunct, ctrsForFun) = getNLConstraints(fd, instVCmodCE, tempVarMap)                                                      
              //instantiate the disjunct
              val cePath = simplifyArithmetic(TemplateInstantiator.instantiate(disjunct, tempVarMap))
              
              //some sanity checks
              if(variablesOf(cePath).exists(TemplateIdFactory.IsTemplateIdentifier _))
                throw IllegalStateException("Found template identifier in counter-example disjunct: "+cePath)
              
              updateSeenPaths(fd, cePath)
              acc :+ ctrsForFun
            })
            if (newctrs.isEmpty) {              
              //give up, only hard paths remaining
              reporter.info("- Exhausted all easy paths !!")
              reporter.info("- Number of remaining hard paths: " + seenPaths.values.foldLeft(0)((acc, elem) => acc + elem.size))
              (None, Map(), tru)
              
            } else {
              //for stats
              if (InferInvariantsPhase.dumpStats) {
                Stats.innerIterations += 1
                Stats.retries += 1
              }
              
              //try this new path, this might be easy to solve
              solveNLConstraints(easyPart, And(newctrs))
            }
          }
          case _ => {            
            (res, newModel, newPart)
          }
        }
      }               
      
      val (res, newModel, newPart) = solveNLConstraints(inputCtr, initialctr)                      
      res  match {
        case None => {
          //here, there are only hard cases remaining 
          None
        }
        case Some(false) => {
          //print some statistics 
          //reporter.info("- Number of explored paths (of the DAG) in this unroll step: " + exploredPaths)
          None
        }
        case Some(true) => {      

          //For debugging
          if (debugIncremental) {
            println("Found a model1: "+newModel)
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
          //new model may not have mappings for all the template variables,
          //use the mappings from earlier models if they exist
          //otherwise, complete them using simplest values
          val compModel = model.keys.map((id) => {
            if (newModel.contains(id))
              (id -> newModel(id))
            else 
              (id -> model(id))            
          }).toMap            
          //println("New model: "+ newModel + " Completed Model: "+compModel)
          recSolve(compModel, funcVCs, And(inputCtr, newPart), solverWithCtr)
        }
      }             
    }
  }   	  
  
  /**
   * Returns the counter example disjunct
   */
  def getNLConstraints(fd: FunDef, instVC : Expr, tempVarMap: Map[Expr,Expr]) : (Expr, Expr) = {
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

    //println("verification condition for" + fd.id + " : " + cande)
    //println("Solution: "+uiSolver.solveSATWithFunctionCalls(cande))

    //this creates a new solver and does not work with the SimpleSolverAPI
    val t1 = System.currentTimeMillis()
    val solEval = new UIFZ3Solver(context, program)
    solEval.assertCnstr(instVC)
    
    solEval.check match {
      case None => {
        solEval.free()
        throw IllegalStateException("cannot check the satisfiability of " + instVC)
      }
      case Some(false) => {
        solEval.free()
        //do not generate any constraints
        (fls, tru)
      }
      case Some(true) => {
        //For debugging purposes.
        println("Function: " + fd.id + "--Found candidate invariant is not a real invariant! ")
        //val counterExample = solEval.getModel
        //println("Counter-example: "+counterExample)

        //try to get the paths that lead to the error 
        val satChooser = (parent: CtrNode, ch: Iterable[CtrTree]) => {
          ch.filter((child) => child match {
            case CtrLeaf() => true
            case cn @ CtrNode(_) => {

              //note the expr may have template variables so replace them with the candidate values
              val nodeExpr = if (!cn.templates.isEmpty) {
                //the node has templates
                TemplateInstantiator.instantiate(cn.toExpr, tempVarMap)
              } else cn.toExpr

              //throw an exception if the expression has reals
              if (InvariantUtil.hasReals(nodeExpr))
                throw IllegalStateException("Node expression has reals: " + nodeExpr)

              solEval.evalBoolExpr(nodeExpr) match {
                case None => throw IllegalStateException("cannot evaluate " + cn.toExpr + " on " + solEval.getModel)
                case Some(b) => b
              }
            }
          })
        }

        //check if two calls (to functions or ADT cons) have the same value in the model 
        val doesAlias = (call1: Expr, call2: Expr) => {
          //first check if the return values are equal
          val BinaryOperator(r1 @ Variable(_), _, _) = call1
          val BinaryOperator(r2 @ Variable(_), _, _) = call2
          val resEquals = solEval.evalBoolExpr(Equals(r1, r2))
          if (resEquals.isEmpty)
            throw IllegalStateException("cannot evaluate " + Equals(r1, r2) + " on " + solEval.getModel)

          if (resEquals.get) {
            //for function calls do additional checks
            if (InvariantUtil.isCallExpr(call1)) {
              val (ants, _) = axiomatizeCalls(call1, call2)
              val antExpr = And(ants)
              solEval.evalBoolExpr(antExpr) match {
                case None => throw IllegalStateException("cannot evaluate " + antExpr + " on " + solEval.getModel)
                case Some(b) => b
              }
            } else {
              //println(Equals(r1, r2) + " evalued to true")
              true
            }
          } else false
        }
        
        val evaluator = (ant: Expr, conseq: Expr) =>
          solEval.evalBoolExpr(ant) match {
            case None => throw IllegalStateException("cannot evaluate " + ant)
            case Some(true) => {
              if(!solEval.evalBoolExpr(conseq).get){
                throw IllegalStateException("ant does not imply conseq")
              }
              true
            }
            case Some(false) => false
          }
          
        val model = solEval.getModel

        //check if two calls satisfy an axiom 
        val generateAxiom = (call1: Expr, call2: Expr) => {

          //check if these are function calls belong to callsWithAxioms 
          //TODO: this is a hack for now
          if (callsWithAxioms.contains(call1) && callsWithAxioms.contains(call2)) {
            val BinaryOperator(r1 @ Variable(_), fi1 @ FunctionInvocation(fd1, args1), _) = call1
            val BinaryOperator(r2 @ Variable(_), fi2 @ FunctionInvocation(fd2, args2), _) = call2
            
            if (this.debugAxioms) {
              println("Calls: (" + call1 + "," + call2 + ")")
              println("Model: " + (args1 ++ args2 ++ Seq(r1, r2)).map((v) => (v, model(v.asInstanceOf[Variable].id))))
            }
            val (ants1, conseq1) = this.monotonizeCalls(call1, call2)
            val ant1 = And(ants1)
            if (evaluator(ant1, conseq1)) {
              //for debugging
              //if(this.debugAxioms)
            	println("Axiom pre implied ")

              Some(And(ant1, conseq1))
            } else {
              val (ants2, conseq2) = this.monotonizeCalls(call2, call1)
              val ant2 = And(ants2)
              if (evaluator(ant2, conseq2)) {
                //for debugging
                //if(this.debugAxioms)
            	  println("Axiom pre implied ")

                Some(And(ant2, conseq2))
              } else {
                //if(this.debugAxioms)
            	  println("Axiom pre not implied ")
                //we need to say that arg1 and arg2 are incomparable
                Some(And(Not(ant1), Not(ant2)))
              }
            }
          } else None
        }

        val (btree, ptree) = ctrTracker.getVC(fd)
        val (newdisjunct, newctr) = generateCtrsForTree(btree, ptree, satChooser, doesAlias, generateAxiom,
        													/**Not used but kept around for debugging**/ solEval)
        if (newctr == tru)
          throw IllegalStateException("cannot find a counter-example path!!")

        //free the solver here
        solEval.free()
        
        //for stats
        val t2 = System.currentTimeMillis()
        val (cum,max) = Stats.cumMax(Stats.cumExploreTime, Stats.maxExploreTime, (t2 - t1))
        Stats.cumExploreTime = cum; Stats.maxExploreTime = max
        
        (newdisjunct, newctr)
      }
	}        
  }
      
  /**
   * Returns a disjunct and a set of non linear constraints whose solution will invalidate the disjunct.
   * This is parametrized by two closure 
   * (a) a child selector function that decides which children to consider.
   * (b) a mayAlias function that decides which function / ADT constructor calls to consider.   
   */
  private def generateCtrsForTree(bodyRoot: CtrNode, postRoot : CtrNode, 
      selector : (CtrNode, Iterable[CtrTree]) => Iterable[CtrTree],
      doesAlias: (Expr, Expr) => Boolean, 
      generateAxiom : (Expr,Expr) => Option[Expr],      
      /**Kept around for debugging **/evalSolver: UIFZ3Solver) : (Expr, Expr) = {
    
    //create an incremental solver, the solver is pushed and popped constraints as the paths in the DNFTree are explored
    //val solver = new UIFZ3Solver(context, program)    
    
    /**
     * A utility function that converts a constraint + calls into a expression.
     * Note: adds the uifs in conjunction to the ctrs
     */    
    def constraintsToExpr(ctrs: Seq[LinearConstraint], calls: Set[Call], auxConjuncts: Seq[Expr]): Expr = {
      val pathExpr = And(ctrs.foldLeft(Seq[Expr]())((acc, ctr) => (acc :+ ctr.expr)))
      val uifExpr = And(calls.map((call) => Equals(call.retexpr,call.fi)).toSeq)
      And(Seq(pathExpr, uifExpr) ++ auxConjuncts)
    }

    /**
     * Traverses the children until one child with a non-true constraint is found
     */
    def traverseChildren(parent: CtrNode, childTrees: Iterable[CtrTree], pred: CtrTree => (Expr, Expr)): (Expr, Expr) = {
      val trees = selector(parent, childTrees)
      var ctr: Expr = tru
      var disjunct: Expr = fls

      breakable {
        trees.foreach((tree) => {
          val res = pred(tree)
          res match {
            case (_, BooleanLiteral(true)) => ;
            case (dis, nlctr) => {
              disjunct = dis
              ctr = nlctr
              break;
            }
          }
        })
      }
      (disjunct, ctr)
    } 

    /**
     * The overall flow:
     * Body --pipe---> post --pipe---> uifConstraintGen --pipe---> endPoint
     */        
    //this tree could have 2^n paths, where 'n' is the number of atomic predicates in the body formula
    def traverseBodyTree(tree: CtrTree, 
        currentCtrs: Seq[LinearConstraint], 
        currentUIFs: Set[Call], 
        currentTemps: Seq[LinearTemplate],
        adtCons : Seq[Expr],
        auxCtrs : Seq[Expr]): (Expr, Expr) = {

      tree match {
        case n @ CtrNode(_) => {
          //println("Traversing Body Tree")
          val addCtrs = n.constraints.toSeq
          val addCalls = n.uifs
          val addCons = n.adtCtrs.collect{ case adtctr@_ if adtctr.cons.isDefined => adtctr.cons.get }.toSeq
          val addAuxs = n.boolCtrs.map(_.expr) ++ n.adtCtrs.collect{ case ac@_ if !ac.cons.isDefined => ac.expr }.toSeq           
          
          //create a path constraint and assert it in the solver
          //solver.push()
          val nodeExpr = constraintsToExpr(addCtrs, addCalls, addCons ++ addAuxs)
          //solver.assertCnstr(nodeExpr)

          //recurse into children and collect all the constraints
          val newCtrs = currentCtrs ++ addCtrs
          val newTemps = currentTemps ++ n.templates
          val newUIFs = currentUIFs ++ addCalls 
          val cons = adtCons ++ addCons          
          val newAuxs = auxCtrs ++ addAuxs                   
          traverseChildren(n, n.Children, (child : CtrTree) =>
            traverseBodyTree(child, newCtrs, newUIFs, newTemps, cons, newAuxs))                             
        }
        case CtrLeaf() => {
          //pipe this to the post tree           
          traversePostTree(postRoot, currentCtrs, currentTemps, auxCtrs, currentUIFs, adtCons, Seq(), Seq(), Seq())
        }
      }
    }
     
    //this tree could have 2^n paths
    def traversePostTree(tree: CtrTree, 
        ants: Seq[LinearConstraint], 
        antTemps: Seq[LinearTemplate],
        antAuxs: Seq[Expr], 
        currUIFs: Set[Call], 
        adtCons : Seq[Expr],
        conseqs: Seq[LinearConstraint], 
        currTemps: Seq[LinearTemplate],        
        currAuxs: Seq[Expr]): (Expr, Expr) = {
          						
      tree match {
        case n @ CtrNode(_) => {          
          //println("Traversing Post Tree")
          val addCtrs = n.constraints.toSeq
          val addCalls = n.uifs 
          val addCons = n.adtCtrs.collect{ case adtctr@_ if adtctr.cons.isDefined => adtctr.cons.get }.toSeq
          val addAuxs = (n.boolCtrs.map(_.expr) ++ n.adtCtrs.collect{ case adtctr@_ if !adtctr.cons.isDefined => adtctr.expr }).toSeq
          
          //create a path constraint and assert it in the solver
          //solver.push()
          val nodeExpr = constraintsToExpr(addCtrs, addCalls, addCons ++ addAuxs)
          //solver.assertCnstr(nodeExpr)

          //recurse into children and collect all the constraints
          val newconstrs = conseqs ++ addCtrs
          val newuifs = currUIFs ++ addCalls 
          val newtemps = currTemps ++ n.templates
          val newCons = adtCons ++  addCons
          val newAuxs = currAuxs ++ addAuxs
          val resExpr = traverseChildren(n, n.Children, (child : CtrTree) => 
            traversePostTree(child, ants, antTemps, antAuxs, newuifs, newCons, newconstrs, newtemps, newAuxs))
          
          //pop the nodeExpr 
          //solver.pop()          
          resExpr
        }
        case CtrLeaf() => {          
          //pipe to the uif constraint generator           
          uifsConstraintsGen(ants, antTemps, antAuxs, currUIFs, adtCons, conseqs, currTemps, currAuxs)
        }
      }
    }
    
    /**
     * Eliminates the calls using the theory of uninterpreted functions
     * this could take 2^(n^2) time
     */
    def uifsConstraintsGen(ants: Seq[LinearConstraint], 
        antTemps: Seq[LinearTemplate], 
        antAuxs: Seq[Expr],
        calls: Set[Call], 
        adtCons: Seq[Expr], 
        conseqs: Seq[LinearConstraint], 
        conseqTemps: Seq[LinearTemplate], 
        conseqAuxs: Seq[Expr]) : (Expr, Expr) = {
      
      def traverseTree(tree: CtrTree, 
         ants: Seq[LinearConstraint], antTemps: Seq[LinearTemplate], 
         conseqs: Seq[LinearConstraint], conseqTemps: Seq[LinearTemplate],
         boolCtrs : Seq[Expr]): (Expr, Expr) = {
        
        tree match {
          case n @ CtrNode(_) => {
            //println("Traversing UIF Tree: node id: "+n.id)                        
            val newants = ants ++ n.constraints         
            val newBools = boolCtrs ++ n.boolCtrs.map(_.expr)
            //note: other constraints are  possible
            
            //recurse into children
            traverseChildren(n, n.Children, (child : CtrTree) => 
              traverseTree(child, newants, antTemps, conseqs, conseqTemps, newBools))
          }
          case CtrLeaf() => {
            //pipe to the end point that invokes the constraint solver
            endpoint(ants, antTemps, conseqs, conseqTemps)
          }
        }
      }

      val pathctr = constraintsToExpr(ants ++ conseqs, calls, adtCons ++ antAuxs ++ conseqAuxs)
      val uifexprs = calls.map((call) => Equals(call.retexpr, call.fi)).toSeq
      //for debugging
      if (this.printPathToConsole || this.dumpPathAsSMTLIB) {
        val pathexprsWithTemplate = (ants ++ antTemps ++ conseqs ++ conseqTemps).map(_.template)
        val plainFormula = And(antAuxs ++ conseqAuxs ++ adtCons ++ uifexprs ++ pathexprsWithTemplate)
        val pathcond = simplifyArithmetic(plainFormula)
        
        if(this.printPathToConsole)
          println("Full-path: " + pathcond)
        /*val wr = new PrintWriter(new File("full-path-"+formula.hashCode()+".txt"))
          ExpressionTransformer.PrintWithIndentation(wr, formula)
          wr.flush()
          wr.close()*/
        
        if(this.dumpPathAsSMTLIB) {
         //create new solver, assert constraints and print
          val printSol = new UIFZ3Solver(context, program)
          printSol.assertCnstr(pathcond)
          val filename = "pathcond"+ FileCountGUID.getID 
          val writer = new PrintWriter(filename)
          writer.println(printSol.ctrsToString("QF_NIA"))
          printSol.free()
          writer.flush()
          writer.close()
        }
      }
      
      val uifCtrs = constraintsForUIFs(uifexprs ++ adtCons, pathctr, doesAlias, generateAxiom)
      val uifroot = if (!uifCtrs.isEmpty) {

        val uifCtr = And(uifCtrs)       
        
        if(this.printCallConstriants) 
          println("UIF constraints: " + uifCtr)
          
        //push not inside
        val nnfExpr = ExpressionTransformer.TransformNot(uifCtr)        
        //check if the two formula's are equivalent
        /*val solver = SimpleSolverAPI(SolverFactory(() => new UIFZ3Solver(context,program)))
        val (res,_) = solver.solveSAT(And(uifCtr,Not(nnfExpr)))
        if(res == Some(false)) 
          println("Both the formulas are equivalent!! ")
         else throw new IllegalStateException("Transformer Formula: "+nnfExpr+" is not equivalent")*/
        /*uifCtrs.foreach((ctr) => {
        	if(evalSolver.evalBoolExpr(ctr) != Some(true))
        		throw new IllegalStateException("Formula not sat by the model: "+ctr)
        })*/
        
        
        //create the root of the UIF tree
        val newnode = CtrNode()
        //add the nnfExpr as a DNF formulae        
        ctrTracker.addConstraintRecur(nnfExpr, newnode)
        newnode

      } else CtrLeaf()
      
      traverseTree(uifroot, ants, antTemps, conseqs, conseqTemps, Seq())           
    }

    /**
     * Endpoint of the pipeline. Invokes the actual constraint solver.
     */
    def endpoint(ants: Seq[LinearConstraint], 
        antTemps: Seq[LinearTemplate],
        conseqs: Seq[LinearConstraint], 
        conseqTemps: Seq[LinearTemplate]): (Expr, Expr) = {      
      //here we are invalidating A^~(B)            
      if (antTemps.isEmpty && conseqTemps.isEmpty) {
        //here ants ^ conseq is sat (otherwise we wouldn't reach here) and there is no way to falsify this path
        (And((ants ++ conseqs).map(_.template)), fls)        
      }
      else {        
        
        val lnctrs = ants ++ conseqs
        val temps = antTemps ++ conseqTemps
        
        if(this.debugElimination)
        	println("Path Constraints (before elim): "+(lnctrs ++ temps))
        
        //TODO: try some optimizations here to reduce the number of constraints to be considered
        //(a) we can eliminate all variables that do not occur in the templates from the lnctrs
        // which are in the theory of presburger arithmetic (we apply only one point rule which is efficient)        
        // Note: this uses the interpolation property of arithmetics        
        
        //compute variables to be eliminated
        val ctrVars = lnctrs.foldLeft(Set[Identifier]())((acc, lc) => acc ++ variablesOf(lc.expr))   
        val tempVars = temps.foldLeft(Set[Identifier]())((acc, lt) => acc ++ variablesOf(lt.template))       
        val elimVars = ctrVars.diff(tempVars)

        //For debugging
        if (debugElimination) {
          reporter.info("Number of linear constraints: " + lnctrs.size)
          reporter.info("Number of template constraints: " + temps.size)
          reporter.info("Number of elimVars: " + elimVars.size)
        }
        
        val elimLnctrs = LinearConstraintUtil.apply1PRuleOnDisjunct(lnctrs, elimVars)

        //for stats
        var elimCtrCount = 0
          var elimCtrs = Seq[LinearConstraint]()
          var elimRems = Set[Identifier]()
          elimLnctrs.foreach((lc) => {
            val evars = variablesOf(lc.expr).intersect(elimVars)
            if (!evars.isEmpty) {
              elimCtrs :+= lc
              elimCtrCount += 1
              elimRems ++= evars
            }
          })
        if (this.debugElimination) {
          reporter.info("Number of linear constraints (after elim): " + elimLnctrs.size)          
          reporter.info("Number of constraints with elimVars: " + elimCtrCount)
          reporter.info("constraints with elimVars: " + elimCtrs)
          reporter.info("Number of remaining elimVars: " + elimRems.size)
          //println("Elim vars: "+elimVars)
          println("Path constriants (after elimination): " + elimLnctrs)                  
        }

        //for stats
        if (InferInvariantsPhase.dumpStats) {
          val (cum1, max1) = Stats.cumMax(Stats.cumElimVars, Stats.maxElimVars, (elimVars.size - elimRems.size))
          Stats.cumElimVars = cum1; Stats.maxElimVars = max1;

          val (cum2, max2) = Stats.cumMax(Stats.cumElimAtoms, Stats.maxElimAtoms, (lnctrs.size - elimLnctrs.size))
          Stats.cumElimAtoms = cum2; Stats.maxElimAtoms = max2;

          val (cum3, max3) = Stats.cumMax(Stats.cumNLsize, Stats.maxNLsize, temps.size)
          Stats.cumNLsize = cum3; Stats.maxNLsize = max3;

          val (cum4, max4) = Stats.cumMax(Stats.cumDijsize, Stats.maxDijsize, lnctrs.size)
          Stats.cumDijsize = cum4; Stats.maxDijsize = max4;
        }         
        
        //(b) drop all constraints with dummys from 'elimLnctrs' they aren't useful (this is because of the reason we introduce the identifiers)
        val newLnctrs = elimLnctrs.filterNot((ln) => variablesOf(ln.expr).exists(TVarFactory.isDummy _))
        
        //TODO: investigate why eliminating variables in not good for constraint solvings
        //val newLnctrs = lnctrs
        
        //TODO: one idea: use the dependence chains in the formulas to identify what to assertionize 
        // and what can never be implied by solving for the templates
        
        if(this.printReducedFormula){
          println("Final Path Constraints: "+(newLnctrs ++ temps))          
        }
        
        val disjunct = And((newLnctrs ++ temps).map(_.template))        
        val implCtrs = farkasSolver.constraintsForUnsat(newLnctrs, temps)
        
        (disjunct, implCtrs)
      }
    }              
    //print the body and the post tree    
    val (disjunct, nlctr) = traverseBodyTree(bodyRoot, Seq(), Set(), Seq(), Seq(), Seq())
    //for debugging
        /*println("NOn linear Ctr: "+nonLinearCtr)
        val (res, model, unsatCore) = uiSolver.solveSATWithFunctionCalls(nonLinearCtr)
              if(res.isDefined && res.get == true){
                println("Found solution for constraints: "+model)
              }*/
    (disjunct, nlctr)    
  }
  
  /**
   * Convert the theory formula into linear arithmetic formula.
   * The calls could be functions calls or ADT constructor calls.
   * The parameter 'doesAliasInCE' is an abbreviation for 'Does Alias in Counter Example'   
   */
  //TODO: important: optimize this code it seems to take a lot of time 
  //TODO: Fix the current incomplete way of handling ADTs and UIFs  
  def constraintsForUIFs(calls: Seq[Expr], precond: Expr, 
      doesAliasInCE : (Expr,Expr) => Boolean,
      generateAxiom : (Expr,Expr) => Option[Expr]) : Seq[Expr] = {
        //solverWithPrecond : UIFZ3Solvers
    var eqGraph = new UndirectedGraph[Expr]() //an equality graph
    var neqSet = Set[(Expr,Expr)]()
    //a mapping from call pairs to the axioms they satisfy
    var axiomSet = Map[(Expr,Expr), Expr]()             
    
    //compute the cartesian product of the calls and select the pairs having the same function symbol and also implied by the precond
    val vec = calls.toArray
    val size = calls.size
    var j = 0
    val product = vec.foldLeft(Set[(Expr, Expr)]())((acc, call) => {

      var pairs = Set[(Expr, Expr)]()
      for (i <- j + 1 until size) {
        val call2 = vec(i)
        if(mayAlias(call,call2)) {
        	pairs ++= Set((call, call2))        
        }        
      }
      j += 1
      acc ++ pairs
    })
    
    //for stats
    reporter.info("Number of compatible calls: "+product.size)     
    val (cum,max) = Stats.cumMax(Stats.cumCompatCalls,Stats.maxCompatCalls, product.size)
    Stats.cumCompatCalls= cum; Stats.maxCompatCalls = max
    
    product.foreach((pair) => {
      val (call1,call2) = (pair._1,pair._2)

      //println("Assertionizing "+call1+" , call2: "+call2)      
      if (!eqGraph.BFSReach(call1, call2)
        && !neqSet.contains((call1, call2))
        && !axiomSet.contains(call1,call2)) {        

        if (doesAliasInCE(call1, call2)) {
          eqGraph.addEdge(call1, call2)          
        } 
        else {
          //check if the call satisfies some of its axioms 
          val axiom = generateAxiom(call1, call2)
          if(axiom.isDefined) {
            axiomSet += (call1,call2) -> axiom.get            
          } else {
        	neqSet ++= Set((call1, call2), (call2, call1))
          }          
        }       
      }
    })    
    
    reporter.info("Number of equal calls: "+eqGraph.getEdgeCount)    
    
    //For equal calls, the constraints are just equalities between the arguments and return values, 
    //For unequal calls, it is the disjunction of disequalities between args   
    val newctrs = product.foldLeft(Seq[Expr]())((acc,pair) => {
      val (call1,call2)= pair
      //note: here it suffices to check for adjacency and not reachability of calls (i.e, exprs).
      //This is because the transitive equalities (corresponding to rechability) are encoded by the generated equalities.
      //This also serves to reduce the generated lambdas
      if(eqGraph.containsEdge(call1,call2)) {
       
        val (lhs, rhs) = if (InvariantUtil.isCallExpr(call1)) {
           //println("Equal calls ")
          axiomatizeCalls(call1, call2)
        } else {
          //here it is an ADT constructor call
          axiomatizeADTCons(call1, call2)
        }
        //remove self equalities.
        val preds = (rhs +: lhs).filter(_ match {
          case BinaryOperator(Variable(lid), Variable(rid), _) => {
            if (lid == rid) false
            else true
          }
          case e @ _ => throw new IllegalStateException("Not an equality or Iff: " + e)
        })                                   
        
        //Finally, removing predicates on ADTs (this introduces incompleteness)
        //TODO: fix this (does not require any big change)
        acc ++ preds.filter((eq) => {
            val BinaryOperator(lhs, rhs, op) = eq
            (lhs.getType == Int32Type || lhs.getType == RealType || lhs.getType == BooleanType)
          })
      }      
      else if(axiomSet.contains(pair)) {
        //here simply add the axiom to the resulting constraints
        acc :+ axiomSet(pair)
      }
      else if(neqSet.contains(pair)) {
               
        //println("unequal calls: "+call1+" , "+call2)
        if(InvariantUtil.isCallExpr(call1)) {
          
          //println("Unequal calls ")
          val (ants,_) = axiomatizeCalls(call1,call2)
          //drop everything if there exists ADTs (note here the antecedent is negated so cannot retain integer predicates)
          //TODO: fix this (this requires mapping of ADTs to integer world and introducing a < total order)
          /*val intEqs = ants.filter((eq) => {
            val BinaryOperator(lhs, rhs, _) = eq
            (lhs.getType == Int32Type || lhs.getType == RealType || lhs.getType == BooleanType)
          })*/                 
          val adtEqs = ants.filter((eq) => if(eq.isInstanceOf[Equals]) {
            val Equals(lhs, rhs) = eq
            (lhs.getType != Int32Type && lhs.getType != RealType && lhs.getType != BooleanType)
          } else false)
          
          if(adtEqs.isEmpty) acc :+ Not(And(ants))
          else {
            //drop everything
            acc
          } 
          
        } else {
          //here call1 and call2 are ADTs                    
          val (lhs,rhs) = axiomatizeADTCons(call1,call2)
          
          val adtEqs = lhs.filter((eq) => if(eq.isInstanceOf[Equals]) {
            val Equals(lhs, rhs) = eq
            (lhs.getType != Int32Type && lhs.getType != RealType && lhs.getType != BooleanType)
          } else false)
          
          //note the rhs is always of ADT type (so we are ignoring it) for completeness we must have 'And(Not(rhs),Not(And(lhs)))'
          //TODO: fix this
          if(adtEqs.isEmpty) acc :+ Not(And(lhs))
          else acc            
        }        
      }        
      else acc
    })       
    newctrs
  }
 
  /**
   * This function actually checks if two non-primitive expressions could have the same value
   * (when some constraints on their arguments hold).
   * Remark: notice  that when the expressions have ADT types, then this is basically a form of may-alias check.
   */
  def mayAlias(e1: Expr, e2: Expr): Boolean = {
    //check if call and call2 are compatible
    (e1, e2) match {
      case (Equals(_, FunctionInvocation(fd1, _)), Equals(_, FunctionInvocation(fd2, _))) if (fd1 == fd2) => true
      case (Iff(_, FunctionInvocation(fd1, _)), Iff(_, FunctionInvocation(fd2, _))) if (fd1 == fd2) => true
      case (Equals(_, CaseClass(cd1, _)), Equals(_, CaseClass(cd2, _))) if (cd1 == cd2) => true
      case (Equals(_, tp1@Tuple(e1)), Equals(_, tp2@Tuple(e2))) if (tp1.getType == tp2.getType) => true
      case _ => false
    }
  }

  /**
   * This procedure generates constraints for the calls to be equal
   */
  def axiomatizeCalls(call1: Expr, call2:  Expr): (Seq[Expr], Expr) = {

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
  def axiomatizeADTCons(sel1: Expr, sel2:  Expr): (Seq[Expr], Expr) = {    

    val (v1, args1, v2, args2) = sel1 match {
      case Equals(r1@Variable(_),CaseClass(_,a1)) => {
        val Equals(r2@Variable(_),CaseClass(_,a2)) = sel2        
        (r1,a1,r2,a2)
      } 
      case Equals(r1@Variable(_),Tuple(a1)) => {
        val Equals(r2@Variable(_),Tuple(a2)) = sel2
        (r1,a1,r2,a2)
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
