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
import leon.solvers.SolverFactory

class LinearSystemAnalyzer(ctrTracker : ConstraintTracker, tempFactory: TemplateFactory,
    context : LeonContext, program : Program) {

  private val reporter = context.reporter
  private val implicationSolver = new LinearImplicationSolver()
  private val cg = CallGraphUtil.constructCallGraph(program)
  
  //some constants
  private val fls = BooleanLiteral(false)
  private val tru = BooleanLiteral(true)
  
  //flags controlling debugging and statistics generation
  //TODO: there is serious bug in using incremental solving. Report this to z3 community
  val debugIncremental = false  
  val debugElimination = false
  val printPaths = false
  val printCallConstriants = false
  val printReducedFormula = false
  val dumpNLFormula = false
  val dumpInstantiatedVC = false
 
  //some utility methods
  def getFIs(ctr: LinearConstraint): Set[FunctionInvocation] = {
    val fis = ctr.coeffMap.keys.collect((e) => e match {
      case fi: FunctionInvocation => fi
    })
    fis.toSet
  }

  /**
   * Completes a model by adding mapping to new template variables
   */
  def completeModel(model: Map[Identifier, Expr], tempIds: Set[Identifier]): Map[Identifier, Expr] = {
    tempIds.map((id) => {
      if (!model.contains(id)) {        
        (id, simplestValue(id.getType))
      } else (id, model(id))
    }).toMap
  }

  /**
   * Computes the invariant for all the procedures given a mapping for the
   * template variables.
   * (Undone) If the mapping does not have a value for an id, then the id is bound to the simplest value
   */
  def getAllInvariants(model: Map[Identifier, Expr]): Map[FunDef, Expr] = {
    val invs = ctrTracker.getFuncs.foldLeft(Seq[(FunDef, Expr)]())((acc, fd) => {

      val tempOption = tempFactory.getTemplate(fd)
      if (!tempOption.isDefined)
        acc
      else {
        //here flatten the template
        val t = tempOption.get
        val freevars = variablesOf(t)
        val template = ExpressionTransformer.FlattenFunction(t)

        val tempvars = InvariantUtil.getTemplateVars(template)
        val tempVarMap: Map[Expr, Expr] = tempvars.map((v) => {
          (v, model(v.id))
        }).toMap

        val instTemplate = instantiateTemplate(template, tempVarMap)
        //now unflatten it
        val comprTemp = ExpressionTransformer.unFlatten(instTemplate, freevars)

        acc :+ (fd, comprTemp)
      }
    })
    invs.toMap
  }

  /**
   * Instantiates templated subexpressions of the given expression (expr) using the given mapping for the template variables.
   * The instantiation also takes care of converting the rational coefficients to integer coefficients.
   */
  def instantiateTemplate(expr: Expr, tempVarMap: Map[Expr, Expr]): Expr = {
    //do a simple post transform and replace the template vars by their values
    val inv = simplePostTransform((tempExpr: Expr) => tempExpr match {
      case e @ BinaryOperator(lhs, rhs, op) if ((e.isInstanceOf[Equals] || e.isInstanceOf[LessThan]
        || e.isInstanceOf[LessEquals] || e.isInstanceOf[GreaterThan]
        || e.isInstanceOf[GreaterEquals]) 
        && 
        !InvariantUtil.getTemplateVars(tempExpr).isEmpty) => {

        //println("Template Expression: "+tempExpr)
        val linearTemp = LinearConstraintUtil.exprToTemplate(tempExpr)
        instantiateTemplate(linearTemp, tempVarMap)
      }
      case _ => tempExpr
    })(expr)
    inv
  }

  def instantiateTemplate(linearTemp: LinearTemplate, tempVarMap: Map[Expr, Expr]): Expr = {
    val coeffMap = linearTemp.coeffTemplate.map((entry) => {
      val (term, coeffTemp) = entry
      val coeffE = replace(tempVarMap, coeffTemp)
      val coeff = RealValuedExprInterpreter.evaluate(coeffE)
      (term -> coeff)
    })
    val const = if (linearTemp.constTemplate.isDefined)
      Some(RealValuedExprInterpreter.evaluate(replace(tempVarMap, linearTemp.constTemplate.get)))
    else None

    val realValues: Seq[Expr] = coeffMap.values.toSeq ++ { if (const.isDefined) Seq(const.get) else Seq() }
    
    //sanity check on real values
    realValues.foreach((rval) => {
    	if(!rval.isInstanceOf[RealLiteral])
    	  throw new IllegalStateException("Not a real value: "+rval)
    	val RealLiteral(num,denom) = rval
    	if(denom == 0)
    	  throw new IllegalStateException("Denominator is zero !! "+rval)
    	if(denom < 0)
    	  throw new IllegalStateException("Denominator is negative: "+denom)
    })

    //the coefficients could be fractions ,so collect all the denominators
    val getDenom = (t: Expr) => t match {
      case RealLiteral(num, denum) => denum
      case _ => 1
    }

    val denoms = realValues.foldLeft(Set[Int]())((acc, entry) => { acc + getDenom(entry) })
    
    //compute the LCM of the denominators
    val gcd = denoms.foldLeft(1)((acc, d) => InvariantUtil.gcd(acc,d))        
    val lcm = denoms.foldLeft(1)((acc, d) => {
      val product = (acc * d)
      if(product % gcd == 0) 
        product/ gcd 
      else product 
    })

    //scale the numerator by lcm
    val scaleNum = (t: Expr) => t match {
      case RealLiteral(num, denum) => IntLiteral(num * (lcm / denum))
      case IntLiteral(n) => IntLiteral(n * lcm)
      case _ => throw IllegalStateException("Coefficient not assigned to any value")
    }
    val intCoeffMap = coeffMap.map((entry) => (entry._1, scaleNum(entry._2)))
    val intConst = if (const.isDefined) Some(scaleNum(const.get)) else None

    val linearCtr = new LinearConstraint(linearTemp.op, intCoeffMap, intConst)
    linearCtr.expr
  }
  
  //for stats
  var exploredPaths = 0   
  var ctrCount = 0 
  /**
   * This function computes invariants belonging to the given templates incrementally.
   * The result is a mapping from function definitions to the corresponding invariants.
   */  
  def solveForTemplatesIncr(): Option[Map[FunDef, Expr]] = {

    //for stats
    exploredPaths = 0
        
    //traverse each of the functions and collect the VCs
    val funcs = ctrTracker.getFuncs
    val funcExprs = funcs.map((fd) => {
      val (btree, ptree) = ctrTracker.getVC(fd)
      val bexpr = TreeUtil.toExpr(btree)
      val pexpr = TreeUtil.toExpr(ptree)
      
      val formula = And(bexpr, pexpr)            
      (fd -> formula)
    }).toMap  
    
    //Assign some values for the template variables at random (actually use the simplest value for the type)
    val tempIds = funcs.foldLeft(Set[Identifier]())((acc, fd) => {
      val tempOption = tempFactory.getTemplate(fd)
      if (!tempOption.isDefined) acc
      else acc ++ variablesOf(tempOption.get)      
    })
    val simplestModel = tempIds.map((id) => (id -> simplestValue(id.toVariable))).toMap
    //create a new solver 
    val solverWithCtrs = new UIFZ3Solver(this.context, program)
    //solverWithCtrs.assertCnstr(tru)
    //for stats
    ctrCount = 0
    
    val solution = recSolveForTemplatesIncr(simplestModel, solverWithCtrs, funcExprs, tru)
    solverWithCtrs.free()
    solution
    //uncomment the following if you want to skip solving but are find with any arbitrary choice
    //Some(getAllInvariants(simplestModel))
  }

  //not deleting since I find the logic used here interesting
  /*
      if(program.isRecursive(fd)) {
        //try pick paths without function calls if any      
        println("Choosing constraints without calls (that are satisfiable)")
        ctr = generateCtrsForTree(btree, ptree, noRecursiveCallSelector(fd), true)
        println("Found Some: " + (ctr != tru))
      }
            
      if (ctr == tru) {        
        //this is going over many iterations in rare scenarios.
        //what if all the paths in the program are infeasible ? may be we should time out after sometime and have some random assignment
        //of values to the terms.
        println("Randomly choosing constraints (that are satisfiable) ...")
        while (ctr == tru) {
          println("Looping...")
          ctr = generateCtrsForTree(btree, ptree, randomSelector, false)
        }
        println("Found one!")
      }      
      
      (acc :+ ctr)
    })      
*/  
  def recSolveForTemplatesIncr(model: Map[Identifier, Expr], solverWithCtrs: UIFZ3Solver, funcExprs: Map[FunDef, Expr],
      nonLinearCtr : Expr)
  	: Option[Map[FunDef, Expr]] = {

    val funcs = funcExprs.keys

    //the following does not seem to be necessary as z3 updates the model on demand
    //val compModel = completeModel(model, TemplateIdFactory.getTemplateIds)
    
    //For debugging: printing the candidate invariants found at this step
    println("candidate Invariants")
    val candInvs = getAllInvariants(model)
    candInvs.foreach((entry) => println(entry._1.id + "-->" + entry._2))

    //check if 'inv' is a 'sufficiently strong' invariant by looking for a counter-example. 
    //if one exists find a path (in each tree) that results in the counter-example and add farkas' 
    //constraints for the path to the constraints to be solved        
    val tempVarMap: Map[Expr, Expr] = model.map((elem) => (elem._1.toVariable, elem._2)).toMap
    
    val newctrs = funcs.foldLeft(Seq[Expr]())((acc, fd) => {

      val instVC = simplifyArithmetic(instantiateTemplate(funcExprs(fd), tempVarMap))

      //For debugging
      if(this.dumpInstantiatedVC) {
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
          acc
        }
        case Some(true) => {
          //For debugging purposes.
          println("Function: " + fd.id + "--Found candidate invariant is not a real invariant! ")
          //println("Counter-example: "+solEval.getModel)

          //try to get the paths that lead to the error 
          val satChooser = (parent: CtrNode, ch: Iterable[CtrTree], d: Int) => {
            ch.filter((child) => child match {
              case CtrLeaf() => true
              case cn @ CtrNode(_) => {

                //note the expr may have template variables so replace them with the candidate values
                val nodeExpr = if (!cn.templates.isEmpty) {
                  //the node has templates
                  instantiateTemplate(cn.toExpr, tempVarMap)
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
              } else{
                //println(Equals(r1, r2) + " evalued to true")
                true
              } 
            } else false
          }
           
          val (btree, ptree) = ctrTracker.getVC(fd)
          val newctr = generateCtrsForTree(btree, ptree, satChooser, doesAlias, true, /**Not used by kept around for debugging**/solEval)
          if (newctr == tru)
            throw IllegalStateException("cannot find a counter-example path!!")

          //free the solver here
          solEval.free()
          acc :+ newctr
        }
      }
    })
    
    //have we found a real invariant ?
    if (newctrs.isEmpty) {
      //yes, hurray
      //print some statistics 
      reporter.info("- Number of explored paths (of the DAG) in this unroll step: " + exploredPaths)

      Some(getAllInvariants(model))
    } else {
      //For statistics.
      //reporter.info("- Number of new Constraints: " + newctrs.size)          
      //call the procedure recursively
      val newctr = And(newctrs)      

      //for stats and debugging
      ctrCount += InvariantUtil.atomNum(newctr)
      println("# of atomic predicates: " + ctrCount)

      //add the new constraints      
      //TODO: There is a serious bug here, report the bug to z3 if it happens again
      solverWithCtrs.assertCnstr(newctr)

      //For debugging
      if (this.dumpNLFormula) {       
        FileCountGUID.fileCount += 1
        val filename = "z3formula-" + FileCountGUID.fileCount + ".smt"
        val pwr = new PrintWriter(filename)
        pwr.println(solverWithCtrs.ctrsToString)
        pwr.flush()
        pwr.close()
        println("Formula printed to File: " + filename)
      }                 
      
      val conjunctedCtr = And(nonLinearCtr,newctr)
      val simpSolver =  SimpleSolverAPI(SolverFactory(() => new UIFZ3Solver(context,program)))                 
    	
      println("solving...")
      val t1 = System.currentTimeMillis()      
      val (res,newModel) = simpSolver.solveSAT(conjunctedCtr)       
      val t2 = System.currentTimeMillis()
      println("solved... in " + (t2 - t1) / 1000.0 + "s")

      //for debugging
      if (debugIncremental) {
        solverWithCtrs.innerCheck        
      }
      res  match {
        case None => None
        case Some(false) => {
          //print some statistics 
          reporter.info("- Number of explored paths (of the DAG) in this unroll step: " + exploredPaths)
          None
        }
        case Some(true) => {      

          //For debugging
          if (debugIncremental) {
            println("Found a model1: "+newModel)
            val model2 = solverWithCtrs.getModel
            println("Found a model2: " + model2)
            solverWithCtrs.push()
            solverWithCtrs.assertCnstr(InvariantUtil.modelToExpr(model2))

            val fn2 = "z3formula-withModel-" + FileCountGUID.fileCount + ".smt"
            val pwr = new PrintWriter(fn2)
            pwr.println(solverWithCtrs.ctrsToString)
            pwr.flush()
            pwr.close()
            println("Formula & Model printed to File: " + fn2)

            solverWithCtrs.pop()
          }                   
          recSolveForTemplatesIncr(newModel, solverWithCtrs, funcExprs, conjunctedCtr)
        }
      }             
    }
  }
      
  /**
   * Returns a set of non linear constraints for the given constraint tree.
   * This is parametrized by two closure 
   * (a) a child selector function that decides which children to consider.
   * (b) a mayAlias function that decides which function / ADT constructor calls to consider.
   */
  def generateCtrsForTree(bodyRoot: CtrNode, postRoot : CtrNode, 
      selector : (CtrNode, Iterable[CtrTree], Int) => Iterable[CtrTree],
      doesAlias: (Expr, Expr) => Boolean, 
      exploreOnePath : Boolean,
      /**Kept around for debugging **/evalSolver: UIFZ3Solver) : Expr = {
    
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
     * A helper function that composes a sequence of CtrTrees using the user-provided operation 
     * and "AND" as the join operation.          
     */
    def foldAND(parent: CtrNode, childTrees : Iterable[CtrTree], pred: CtrTree => Expr, depth: Int): Expr = {            
      val trees = selector(parent, childTrees, depth)
      var expr: Expr = tru
      breakable {
        trees.foreach((tree) => {
          val res = pred(tree)
          res match {
            case BooleanLiteral(false) => {
              expr = fls;
              break;
            }
            case BooleanLiteral(true) => ;
            case _ => {
              if (expr == tru) {
                expr = res
                //break if explore one path is set
                if (exploreOnePath) {
                  break;
                }
              } else expr = And(expr, res)
            }
          }
        })
      }
      expr
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
        auxCtrs : Seq[Expr],         
        depth : Int): Expr = {

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
          val resExpr = foldAND(n, n.Children, (child : CtrTree) => 
            traverseBodyTree(child, newCtrs, newUIFs, newTemps, cons, newAuxs, depth + 1), depth)
          
          //pop the nodeExpr 
          //solver.pop()
          
          resExpr
        }
        case CtrLeaf() => {
          //pipe this to the post tree           
          traversePostTree(postRoot, currentCtrs, currentTemps, auxCtrs, currentUIFs, adtCons, Seq(), Seq(), Seq(), depth + 1)
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
        currAuxs: Seq[Expr], depth: Int): Expr = {
          						
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
          val resExpr = foldAND(n, n.Children, (child : CtrTree) => 
            traversePostTree(child, ants, antTemps, antAuxs, newuifs, newCons, newconstrs, newtemps, newAuxs, depth + 1), 
            depth)
          
          //pop the nodeExpr 
          //solver.pop()          
          resExpr
        }
        case CtrLeaf() => {
          //pipe to the uif constraint generator           
          uifsConstraintsGen(ants, antTemps, antAuxs, currUIFs, adtCons, conseqs, currTemps, currAuxs, depth + 1)
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
        conseqAuxs: Seq[Expr], depth: Int) : Expr = {
      
      def traverseTree(tree: CtrTree, 
         ants: Seq[LinearConstraint], antTemps: Seq[LinearTemplate], 
         conseqs: Seq[LinearConstraint], conseqTemps: Seq[LinearTemplate],
         boolCtrs : Seq[Expr],
         dep: Int): Expr = {
        
        tree match {
          case n @ CtrNode(_) => {
            //println("Traversing UIF Tree: node id: "+n.id)                        
            val newants = ants ++ n.constraints         
            val newBools = boolCtrs ++ n.boolCtrs.map(_.expr)
            //note: other constraints are  possible
            
            //recurse into children
            foldAND(n, n.Children, (child : CtrTree) => traverseTree(child, newants, antTemps, conseqs, conseqTemps, newBools, dep + 1), dep)
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
      if (this.printPaths) {
        val pathexprsWithTemplate = (ants ++ antTemps ++ conseqs ++ conseqTemps).map(_.template)
        val plainFormula = And(antAuxs ++ conseqAuxs ++ adtCons ++ uifexprs ++ pathexprsWithTemplate)
        val formula = simplifyArithmetic(plainFormula)
        println("Full-path: " + formula)
        /*val wr = new PrintWriter(new File("full-path-"+formula.hashCode()+".txt"))
          ExpressionTransformer.PrintWithIndentation(wr, formula)
          wr.flush()
          wr.close()*/
      }
      
      val uifCtrs = constraintsForUIFs(uifexprs ++ adtCons, pathctr, doesAlias)
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
      
      traverseTree(uifroot, ants, antTemps, conseqs, conseqTemps, Seq(), depth)           
    }

    /**
     * Endpoint of the pipeline. Invokes the actual constraint solver.
     */
    def endpoint(ants: Seq[LinearConstraint], 
        antTemps: Seq[LinearTemplate],
        conseqs: Seq[LinearConstraint], 
        conseqTemps: Seq[LinearTemplate]): Expr = {      
      //here we are solving A^~(B)      
      if (conseqs.isEmpty && conseqTemps.isEmpty) tru
      else if (antTemps.isEmpty && conseqTemps.isEmpty) {
        //here ants ^ conseq is sat (otherwise we wouldn't reach here) and there is no way to falsify this path
        fls        
      }
      else {
        exploredPaths += 1
        
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

        if (this.debugElimination) {
          reporter.info("Number of linear constraints (after elim): " + elimLnctrs.size)
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
          reporter.info("Number of constraints with elimVars: " + elimCtrCount)
          reporter.info("constraints with elimVars: " + elimCtrs)
          reporter.info("Number of remaining elimVars: " + elimRems.size)
          //println("Elim vars: "+elimVars)
          println("Path constriants (after elimination): " + elimLnctrs)
        }
        
        //(b) drop all constraints with dummys from 'elimLnctrs' they aren't useful (this is because of the reason we introduce the identifiers)
        val newLnctrs = elimLnctrs.filterNot((ln) => variablesOf(ln.expr).exists(TempIdFactory.isDummy _))
        
        //TODO: investigate why eliminating variables in not good for constraint solvings
        //val newLnctrs = lnctrs
        
        //TODO: one idea: use the dependence chains in the formulas to identify what to assertionize 
        // and what can never be implied by solving for the templates
        
        if(this.printReducedFormula)
        	println("Final Path Constraints: "+(newLnctrs ++ temps))
        	
        val implCtrs = implicationSolver.constraintsForUnsat(newLnctrs, temps)        
        implCtrs
      }
    }              
    //print the body and the post tree    
    val nonLinearCtr = traverseBodyTree(bodyRoot, Seq(), Set(), Seq(), Seq(), Seq(), 0)    
    nonLinearCtr match {
      case BooleanLiteral(true) => tru       
      case _ => {
        //for debugging
        /*println("NOn linear Ctr: "+nonLinearCtr)
        val (res, model, unsatCore) = uiSolver.solveSATWithFunctionCalls(nonLinearCtr)
              if(res.isDefined && res.get == true){
                println("Found solution for constraints: "+model)
              }*/
        nonLinearCtr
      }
    }    
  }
  
  /**
   * Convert the theory formula into linear arithmetic formula.
   * The calls could be functions calls or ADT constructor calls.
   * The parameter 'doesAliasInCE' is an abbreviation for 'Does Alias in Counter Example'   
   */
  //TODO: important: optimize this code it seems to take a lot of time 
  //TODO: Fix the current incomplete way of handling ADTs and UIFs  
  def constraintsForUIFs(calls: Seq[Expr], precond: Expr, doesAliasInCE : (Expr,Expr) => Boolean) : Seq[Expr] = {
        //solverWithPrecond : UIFZ3Solvers
    var eqGraph = new UndirectedGraph[Expr]() //an equality graph
    var neqSet = Set[(Expr,Expr)]()
    //var cannotEqSet = Set[(Expr,Expr)]()           
    
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
    
    reporter.info("Number of compatible calls: "+product.size)             
    
    product.foreach((pair) => {
      val (call1,call2) = (pair._1,pair._2)

      //println("Assertionizing "+call1+" , call2: "+call2)      
      if (!eqGraph.BFSReach(call1, call2)
        && !neqSet.contains((call1, call2))) {        

        if (doesAliasInCE(call1, call2)) {
          eqGraph.addEdge(call1, call2)
        } else {
          neqSet ++= Set((call1, call2), (call2, call1))
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

        //println("Equal calls: "+call1+" , "+call2)
        val (lhs, rhs) = if (InvariantUtil.isCallExpr(call1)) {
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
      else if(neqSet.contains(pair)) {
               
        //println("unequal calls: "+call1+" , "+call2)
        if(InvariantUtil.isCallExpr(call1)) {
                   
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
