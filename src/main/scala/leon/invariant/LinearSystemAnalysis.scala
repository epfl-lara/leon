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
          //println(v.id +" mapsto " + model(v.id))         
         /* if(!model.contains(v.id))          
          {
            reporter.warning("- Model does not have a mapping for template varaiable: "+v)
            (v, simplestValue(v))
          }
          else*/
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
        val linearTemp = ctrTracker.exprToTemplate(tempExpr)
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

    //the coefficients could be fractions ,so collect all the denominators
    val getDenom = (t: Expr) => t match {
      case RealLiteral(num, denum) => denum
      case _ => 1
    }

    val denoms = realValues.foldLeft(Set[Int]())((acc, entry) => { acc + getDenom(entry) })
    //compute the LCM of the denominators (approx. LCM)
    val lcm = denoms.foldLeft(1)((acc, d) => if (acc % d == 0) acc else acc * d)

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

  /**
   * This function computes invariants belonging to the given templates.
   * The result is a mapping from function definitions to the corresponding invariants.
   */
  var exploredPaths = 0
  def solveForTemplates(uiSolver: SimpleSolverAPI): Option[Map[FunDef, Expr]] = {
  
    exploredPaths = 0
    
    val selector = (p: CtrNode, ch: Iterable[CtrTree],d: Int) => ch
    //traverse each of the functions and collect the constraints
    val nonLinearCtrs  = ctrTracker.getFuncs.foldLeft(Seq[Expr]())((acc, fd) => {
      
      val (btree,ptree) = ctrTracker.getVC(fd)      
      val ctr = generateCtrsForTree(btree, ptree, selector, false)      
      if(ctr == tru) acc        
      else (acc :+ ctr)
    })   
    
    val nonLinearCtr = if(nonLinearCtrs.isEmpty) throw IllegalStateException("Found no constraints") 
    					else if(nonLinearCtrs.size == 1) nonLinearCtrs(0) 
						else And(nonLinearCtrs)
	          
    val (res, model) = uiSolver.solveSAT(nonLinearCtr)
    
    //print some statistics 
    reporter.info("- Number of explored paths (of the DAG) in this unroll step: "+exploredPaths)
    if (res.isDefined && res.get == true) {
      //printing the model here for debugging
      //println("Model: "+model)
      //construct an invariant (and print the model)      
      Some(getAllInvariants(model))
    } else {
      //println("Constraint Unsat: " + unsatCore)
      None
    }	  
  }

  /**
   * This function computes invariants belonging to the given templates incrementally.
   * The result is a mapping from function definitions to the corresponding invariants.
   */
  //for stats
  var ctrCount = 0 
  //used for selecting children  
  val max_depth = -1
  
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
      //println("Formula: "+fd.id+"-->"+formula)
      (fd -> formula)
    }).toMap  

    //A selector that explores only paths that do not have any recursive function calls
    //these, typically correspond to base cases  (and also result in linear constraints)
    /*val noRecursiveCallSelector = (fd: FunDef) => {           
      //find the set of all callers of fd
      val callers = funcs.filter((cr) => cg.transitivelyCalls(cr, fd)).toSet      
      (parent: CtrNode, ch: Iterable[CtrTree], d: Int) => {        
        //check if any of the function called by the parent node transitively calls the  current function
        //println("Checking againt callers... ")
          if (parent.uifs.filter((call) => callers.contains(call.fi.funDef)).isEmpty) 
            ch.toSet
          else Set()
        }
    }
        
    //A selector that picks children at random
    //associate a random number number generator with each node in the tree.
    var randGenMap = Map[CtrNode,Random]()
    val randomSelector = (parent: CtrNode, ch: Iterable[CtrTree], d: Int) => {
      if (d <= max_depth) ch
      else {

        val chIndex = if (randGenMap.contains(parent)) randGenMap(parent).nextInt(ch.size)
        else {
          val randgen = new Random()
          randGenMap += (parent -> randgen)
          randgen.nextInt(ch.size)
        }       
        val child = ch.toSeq.apply(chIndex)
        //print(parent.id+" ---> "+ (if(child.isInstanceOf[CtrNode]) child.asInstanceOf[CtrNode].id else "leaf"))
        Set(child)
      }
    }*/
    
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
  }

  /*def solveForTemplatesIncr(): Option[Map[FunDef, Expr]] = {

    //for stats
    exploredPaths = 0
        
    //traverse each of the functions and collect the VCs
    val funcs = ctrTracker.getFuncs
    val funcExprs = funcs.map((fd) => {
      val (btree, ptree) = ctrTracker.getVC(fd)
      val bexpr = TreeUtil.toExpr(btree)
      val pexpr = TreeUtil.toExpr(ptree)
      
      val formula = And(bexpr, pexpr)      
      //println("Formula: "+fd.id+"-->"+formula)
      (fd -> formula)
    }).toMap
    //System.exit(0)

    //A selector that explores only paths that do not have any recursive function calls
    //these, typically correspond to base cases  (and also result in linear constraints)
    val noRecursiveCallSelector = (fd: FunDef) => {           
      //find the set of all callers of fd
      val callers = funcs.filter((cr) => cg.transitivelyCalls(cr, fd)).toSet      
      (parent: CtrNode, ch: Iterable[CtrTree], d: Int) => {        
        //check if any of the function called by the parent node transitively calls the  current function
        //println("Checking againt callers... ")
          if (parent.uifs.filter((call) => callers.contains(call.fi.funDef)).isEmpty) 
            ch.toSet
          else Set()
        }
    }
        
    //A selector that picks children at random
    //associate a random number number generator with each node in the tree.
    var randGenMap = Map[CtrNode,Random]()
    val randomSelector = (parent: CtrNode, ch: Iterable[CtrTree], d: Int) => {
      if (d <= max_depth) ch
      else {

        val chIndex = if (randGenMap.contains(parent)) randGenMap(parent).nextInt(ch.size)
        else {
          val randgen = new Random()
          randGenMap += (parent -> randgen)
          randgen.nextInt(ch.size)
        }       
        val child = ch.toSeq.apply(chIndex)
        //print(parent.id+" ---> "+ (if(child.isInstanceOf[CtrNode]) child.asInstanceOf[CtrNode].id else "leaf"))
        Set(child)
      }
    }
       
    //incrementally solve for the template variables
    val nonLinearCtrs = funcs.foldLeft(Seq[Expr]())((acc, fd) => {

      val (btree, ptree) = ctrTracker.getVC(fd)
      
      //iterate as long as we have atleast one constraint (using imperative style as it is best fit here)
      var ctr : Expr = tru
      
      if(program.isRecursive(fd)) {
        //try pick paths without function calls if any      
        println("Choosing constraints without calls (that are satisfiable)")
        ctr = generateCtrsForTree(btree, ptree, noRecursiveCallSelector(fd), true)
        println("Found Some: " + (ctr != tru))
      }
            
      if (ctr == tru) {        
        //this is going over many iterations in rare scenarios
        //TODO: critical : how to fix this ??
        //TODO: what if all the paths in the program are infeasible ? may be we should time out after sometime and have some random assignment
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
    
    //For debugging purposes.
    println("# of initals Constraints: "+nonLinearCtrs.size)      
    
    val nonLinearCtr = if (nonLinearCtrs.size == 1) nonLinearCtrs(0)
    					else And(nonLinearCtrs)
    					
    //create a new solver and add the constraints 
    val solverWithCtrs = new UIFZ3Solver(this.context, program)
    solverWithCtrs.assertCnstr(nonLinearCtr)
    
    //for stats
    ctrCount = InvariantUtil.atomNum(nonLinearCtr)
    
    val solution = recSolveForTemplatesIncr(solverWithCtrs, funcExprs)
    solverWithCtrs.free()
    solution
  }
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

    //val wr = new PrintWriter(new File("formula-dump.txt"))
    val newctrs = funcs.foldLeft(Seq[Expr]())((acc, fd) => {

      val instVC = simplifyArithmetic(instantiateTemplate(funcExprs(fd), tempVarMap))

      //For debugging
      /*if(fd.id.name.equals("reverse")) {
            println("Post of " + fd.id + " is: " + instantiateTemplate(TreeUtil.toExpr(ctrTracker.getVC(fd)._2), tempVarMap))            
            System.out.flush()
          }*/

      /*println("Instantiated VC of " + fd.id + " is: " + instVC)*/
      /* wr.println("Function name: " + fd.id)
          wr.println("Formula expr: ")
          ExpressionTransformer.PrintWithIndentation(wr, instVC)
          wr.flush()*/

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
          val (btree, ptree) = ctrTracker.getVC(fd)
          val newctr = generateCtrsForTree(btree, ptree, satChooser, true)
          if (newctr == tru)
            throw IllegalStateException("cannot find a counter-example path!!")

          //free the solver here
          solEval.free()
          acc :+ newctr
        }
      }
    })
    /*wr.flush()
        wr.close()*/

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
      //TODO: Report the bug to z3
      solverWithCtrs.assertCnstr(newctr)
      //println("Assertions: \n"+solverWithCtrs.ctrsToString)               
      /*FileCountGUID.fileCount += 1
      val filename = "z3formula-" + FileCountGUID.fileCount + ".smt"
      val pwr = new PrintWriter(filename)
      pwr.println(solverWithCtrs.ctrsToString)
      pwr.flush()
      pwr.close()
      println("Formula printed to File: " + filename)*/
      
      /*val asserts = solverWithCtrs.solver.getAssertions()
      val newsolver = new UIFZ3Solver(context,program)      
      val expr = asserts.toSeq.foldLeft(tru : Expr)((acc, assert) => And(acc,solverWithCtrs.fromZ3Formula(null,assert)))
      newsolver.assertCnstr(expr)*/            
      
      val conjunctedCtr = And(nonLinearCtr,newctr)
      val simpSolver =  SimpleSolverAPI(SolverFactory(() => new UIFZ3Solver(context,program)))      
    	
      println("solving...")
      val t1 = System.currentTimeMillis()      
      //val res1 = newsolver.innerCheck
      val (res,newModel) = simpSolver.solveSAT(conjunctedCtr)
      val t2 = System.currentTimeMillis()
      println("solved... in " + (t2 - t1) / 1000.0 + "s")
      
      res  match {
        case None => None
        case Some(false) => {
          //print some statistics 
          reporter.info("- Number of explored paths (of the DAG) in this unroll step: " + exploredPaths)
          None
        }
        case Some(true) => {          
          /*println("Found a model1: "+newModel)
          println("Found a model2: "+newsolver.getModel)
          newsolver.free()*/
          recSolveForTemplatesIncr(newModel, solverWithCtrs, funcExprs, conjunctedCtr)
        }
      }      
       
    }
  }
  
  
  /*def recSolveForTemplatesIncr(solverWithCtrs: UIFZ3Solver, uiSolver: SimpleSolverAPI, funcExprs: Map[FunDef, Expr])
  			: Option[Map[FunDef, Expr]] = {

    val funcs = funcExprs.keys

    println("solving...")       
    val t1 = System.currentTimeMillis()

    //println("Assertions: \n"+solverWithCtrs.ctrsToString)               
    FileCountGUID.fileCount += 1
    val pwr = new PrintWriter("z3formula-"+FileCountGUID.fileCount+".smt")    
    pwr.println(solverWithCtrs.ctrsToString)
    pwr.flush()
    pwr.close()
    
    val (res, model) = solverWithCtrs.check match {
      case Some(true) =>
        (Some(true), solverWithCtrs.getModel)
      case Some(false) =>
        (Some(false), Map[Identifier, Expr]())
      case None =>
        (None, Map[Identifier, Expr]())
    }
    
    val t2 = System.currentTimeMillis()
    println("solved... in "+(t2 - t1) / 1000.0+"s")    
    
    res match {
      case None => None
      case Some(false) =>  {
        
        //print some statistics 
    	reporter.info("- Number of explored paths (of the DAG) in this unroll step: "+exploredPaths)
        None
      }
      case Some(true) => {
        //the following does not seem to be necessary as z3 updates the model on demand
        //val compModel = completeModel(model, TemplateIdFactory.getTemplateIds)
        
        //For debugging: printing the candidate invariants found at this step
        println("candidate Invariants")
        val candInvs = getAllInvariants(model)
        candInvs.foreach((entry) => println(entry._1.id + "-->" + entry._2))

        //check if 'inv' is a 'sufficiently strong' invariant by looking for a counter-example. 
        //if one exists find a path (in each tree) that results in the counter-example and add farkas' 
        //constraints for the path to the constraints to be solved        
        val tempVarMap: Map[Expr, Expr] = model.map((elem) => (elem._1.toVariable,elem._2)).toMap

       val wr = new PrintWriter(new File("formula-dump.txt"))
        val newctrs = funcs.foldLeft(Seq[Expr]())((acc, fd) => {
          
          val instVC = simplifyArithmetic(instantiateTemplate(funcExprs(fd), tempVarMap))                   
        
          //For debugging
          if(fd.id.name.equals("reverse")) {
            println("Post of " + fd.id + " is: " + instantiateTemplate(TreeUtil.toExpr(ctrTracker.getVC(fd)._2), tempVarMap))            
            System.out.flush()
          }
            
          println("Instantiated VC of " + fd.id + " is: " + instVC)          
          wr.println("Function name: " + fd.id)
          wr.println("Formula expr: ")
          ExpressionTransformer.PrintWithIndentation(wr, instVC)
          wr.flush()

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
              val (btree, ptree) = ctrTracker.getVC(fd)
              val newctr = generateCtrsForTree(btree, ptree, satChooser, true)
              if(newctr == tru)
                throw IllegalStateException("cannot find a counter-example path!!")
              
              //free the solver here
              solEval.free()
              acc :+ newctr
            }
          }
        })
        wr.flush()
        wr.close()
        
        //have we found a real invariant ?
        if(newctrs.isEmpty) {
          //yes, hurray
          //print some statistics 
          reporter.info("- Number of explored paths (of the DAG) in this unroll step: "+exploredPaths)
           
          Some(getAllInvariants(model))          
        } else {
          //For statistics.
          //reporter.info("- Number of new Constraints: " + newctrs.size)          
          //call the procedure recursively
          val newctr = And(newctrs)          
          
          //for stats and debugging
          ctrCount += InvariantUtil.atomNum(newctr)
          println("# of atomic predicates: "+ctrCount)
                                       
          //add the new constraints
          solverWithCtrs.assertCnstr(newctr)
          recSolveForTemplatesIncr(solverWithCtrs, uiSolver, funcExprs)
        }
      }
    }
  }
  */
  /**
   * Returns a set of non linear constraints for the given constraint tree.
   * This is parametrized by a selector function that decides which paths to consider. 
   */
  def generateCtrsForTree(bodyRoot: CtrNode, postRoot : CtrNode, 
      selector : (CtrNode, Iterable[CtrTree], Int) => Iterable[CtrTree],
      exploreOnePath : Boolean) : Expr = {
    
    //create an incremental solver, the solver is pushed and popped constraints as the paths in the DNFTree are explored
    val solver = new UIFZ3Solver(context, program)
    
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
     * TODO: Maintenance Issue: The following code is imperative
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
          solver.push()
          val nodeExpr = constraintsToExpr(addCtrs, addCalls, addCons ++ addAuxs)
          solver.assertCnstr(nodeExpr)

          //recurse into children and collect all the constraints
          val newCtrs = currentCtrs ++ addCtrs
          val newTemps = currentTemps ++ n.templates
          val newUIFs = currentUIFs ++ addCalls 
          val cons = adtCons ++ addCons          
          val newAuxs = auxCtrs ++ addAuxs                   
          val resExpr = foldAND(n, n.Children, (child : CtrTree) => 
            traverseBodyTree(child, newCtrs, newUIFs, newTemps, cons, newAuxs, depth + 1), depth)
          
          //pop the nodeExpr 
          solver.pop()
          
          resExpr
        }
        case CtrLeaf() => {

          //val pathexpr = constraintsToExpr(currentCtrs, currentUIFs, adtCons ++ auxCtrs)
          //println("Body-path: "+pathexpr)
          //val (res, model) = uiSolver.solveSAT(pathexpr)
          val res = solver.check
          if (!res.isDefined || res.get == true) {

            //println("Body path expr: " + pathexpr)            
            //pipe this to the post tree           
            traversePostTree(postRoot, currentCtrs, currentTemps, auxCtrs, currentUIFs, adtCons, Seq(), Seq(), Seq(), depth + 1)                                      
          } else {
            //println("Found unsat path: " + pathExpr)
            throw new IllegalStateException("Found unsat path!! ")
            tru
          }
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
          solver.push()
          val nodeExpr = constraintsToExpr(addCtrs, addCalls, addCons ++ addAuxs)
          solver.assertCnstr(nodeExpr)

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
          solver.pop()
          
          resExpr
        }
        case CtrLeaf() => {                 

          val res = solver.check
          if (!res.isDefined || res.get == true) {

            //println("path after post traversal: "+constraintsToExpr(ants ++ conseqs, currUIFs, And(antAuxs ++ currAuxs)))            
            //pipe to the uif constraint generator           
            uifsConstraintsGen(ants, antTemps, antAuxs, currUIFs, adtCons, conseqs, currTemps, currAuxs, depth + 1)                                      
          } else {
            throw new IllegalStateException("Found unsat path!! ")
            tru
          }
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
         dep: Int): Expr = {
        
        tree match {
          case n @ CtrNode(_) => {
            //println("Traversing UIF Tree")            
            //recurse into children
            val newants = ants ++ n.constraints                        
            foldAND(n, n.Children, (child : CtrTree) => traverseTree(child, newants, antTemps, conseqs, conseqTemps, dep + 1), dep)
          }
          case CtrLeaf() => {            
            //pipe to the end point that invokes the constraint solver
            endpoint(ants,antTemps,conseqs,conseqTemps)
          }
        }
      }

      val pathctr = constraintsToExpr(ants ++ conseqs, calls, adtCons ++ antAuxs ++ conseqAuxs)
      val uifexprs = calls.map((call) => Equals(call.retexpr, call.fi)).toSeq
      
      //println("path: "+pathexpr)
      //if the path expression is unsatisfiable return true
      /*val (res, model) = uiSolver.solveSAT(pathexpr)
      if (res.isDefined && res.get == false) {
        tru            
      } else {*/      
      //for debugging
      //println("Full-path: " + simplifyArithmetic(pathexpr))
      //println("All ctrs: "+ (ants ++ conseqs ++ calls ++ conseqTemps))      
      val pathexprsWithTemplate = (ants ++ antTemps ++ conseqs ++ conseqTemps).map(_.template)
      val plainFormula = And(antAuxs ++ conseqAuxs ++ adtCons ++ uifexprs ++ pathexprsWithTemplate)
      val formula = simplifyArithmetic(plainFormula)
      /*val wr = new PrintWriter(new File("full-path-"+formula.hashCode()+".txt"))
          ExpressionTransformer.PrintWithIndentation(wr, formula)
          wr.flush()
          wr.close()*/
      println("Full-path: " + formula)

      //println("Starting Constraint generation")
      val uifCtrs = constraintsForUIFs(uifexprs ++ adtCons, pathctr, solver)
      //println("Generated UIF Constraints")

      val uifroot = if (!uifCtrs.isEmpty) {

        val uifCtr = And(uifCtrs)
        println("UIF constraints: " + uifCtr)
        //push not inside
        val nnfExpr = ExpressionTransformer.TransformNot(uifCtr)
        //create the root of the UIF tree
        val newnode = CtrNode()
        //add the nnfExpr as a DNF formulae
        ctrTracker.addConstraintRecur(nnfExpr, newnode)
        newnode

      } else CtrLeaf()
      //fls
      traverseTree(uifroot, ants, antTemps, conseqs, conseqTemps, depth)  
      //}      
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
                
        println("Final Path Constraints: "+And((ants ++ antTemps ++ conseqs ++ conseqTemps).map(_.template)))
        val implCtrs = implicationSolver.constraintsForUnsat(ants, antTemps, conseqs, conseqTemps)        
        implCtrs
      }
    }       
       
    //print the body and the post tree    
    val nonLinearCtr = traverseBodyTree(bodyRoot, Seq(), Set(), Seq(), Seq(), Seq(), 0)
    
    //free the solver
    solver.free()

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
  
  //convert the theory formula into linear arithmetic formula
  //TODO: very very important: optimize this code it seems to take a lot of time 
  //TODO: Fix the current incomplete way of handling ADTs
  //TODO: For efficiency, consider only functions with integer return type
  //TODO: one idea: use the dependence chains in the formulas to identify what to assertionze and what can never be implied
  // by solving for the templates
  def constraintsForUIFs(calls: Seq[Expr], precond: Expr, solverWithPrecond : UIFZ3Solver) : Seq[Expr] = {
        
    //Part(I): Finding the set of all pairs of calls (or expressions) that are implied by the precond
    var eqGraph = new UndirectedGraph[Expr]() //an equality graph
    var neqSet = Set[(Expr,Expr)]()
    var cannotEqSet = Set[(Expr,Expr)]()           
    
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
    
    var smtCalls = 0
    def isImplied(cond: Expr): TVL.Value = {
      //For stats
      smtCalls += 1

      //check if the not(precond => cond) (i.e, precond^not(cond)) is unsat
      solverWithPrecond.push()
      solverWithPrecond.assertCnstr(Not(cond))
      val nImpRes = solverWithPrecond.check
      solverWithPrecond.pop()

      nImpRes match {
        case Some(false) => TVL.TRUE
        case _ => {
          //check if (precond => not(cond)) is valid (i.e, not(precond ^ cond) is unsat)
          solverWithPrecond.push()
          solverWithPrecond.assertCnstr(cond)
          val impRes = solverWithPrecond.check
          solverWithPrecond.pop()

          impRes match {
            case Some(false) => TVL.FALSE
            case _ => TVL.MAYBE
          }
        }
      }
    }

    /**
     * Requires 'e' to be a cojunction of equalities.
     * Returns a set of ADT equalities in the input expression
     */
    def ADTequalities(eqs: Seq[Expr]): Seq[Expr] = {
      eqs.filter((eq) => {
        val BinaryOperator(lhs, rhs, _) = eq
        (lhs.getType != Int32Type && lhs.getType != BooleanType && lhs.getType != RealType)
      })
    }
    
    product.foreach((pair) => {
      val (call1,call2) = (pair._1,pair._2)

      //println("Assertionizing "+call1+" , call2: "+call2)      
      if (!eqGraph.BFSReach(call1, call2)
        && !neqSet.contains((call1, call2))
        && !cannotEqSet.contains((call1, call2))) {

        if (InvariantUtil.isCallExpr(call1)) {
          val (ants, conseq) = axiomatizeCalls(call1, call2)
          val tv = isImplied(And(ants))
          if (tv == TVL.FALSE) {
            //here the arg. equality will never be implied by the precond (unless the precond becomes false). 
            //Therefore we can drop this constraint           
            cannotEqSet ++ Set((call1, call2), (call2, call1))
          } else if (tv == TVL.TRUE) {
            //here the argument equality follows from the precondition
            eqGraph.addEdge(call1, call2)
          } else {
            //here the argument equality does not follow from the precondition but may be implied by instantiation of the templates
            //TODO: try some optimizations here, write down the ideas here
            //(a) consider the following optimization :
            //take the model found in this case. If the instantiation of the template does not satisfy the model
            //then may be it could imply the equality. So, we could try this case later.              

            //An incomplete efficiency heuristic
            //If the adt equalities in ant is not implied by precond then drop this call (incompletely assume
            // that templates cannot make them equal), this is true when the adts are inputs
            val adtEqs = ADTequalities(ants)

            //check if not(precond => And(adtEqs)) is unsat
            solverWithPrecond.push()
            solverWithPrecond.assertCnstr(Not(And(adtEqs)))
            val adtImp = solverWithPrecond.check
            solverWithPrecond.pop()

            if (adtImp.isDefined && adtImp.get == true) {
              //here the implication need not necessarily hold therefore we consider that it can never 
              //hold (assuming that the templates do not affect ADTs values through integers)
              cannotEqSet ++ Set((call1, call2), (call2, call1))
            } else {
              neqSet ++= Set((call1, call2), (call2, call1))
            }
          }
        } else if (InvariantUtil.isADTConstructor(call1)) {

          val (lhs, rhs) = axiomatizeADTCons(call1, call2)

          //the two expressions are equal (or notequal) either if lhs are equal (or notequal) or if rhs are equal (or notequal)            
          val tv1 = isImplied(rhs)
          val tv2 = if (tv1 == TVL.MAYBE) isImplied(And(lhs))            
          			else TVL.MAYBE
          //note that since the formula is consistent, tv1 and tv2 must compatible i.e, one cannot be true and other false
          if (tv1 == TVL.TRUE || tv2 == TVL.TRUE) {
            eqGraph.addEdge(call1, call2)

          } else if (tv1 == TVL.FALSE || tv2 == TVL.FALSE) {
            cannotEqSet ++ Set((call1, call2), (call2, call1)) //drop this
          } else {
            //here both are maybe, for now, drop this too
            //TODO: Fix this
            cannotEqSet ++ Set((call1, call2), (call2, call1))
            //neqSet ++= Set((call1, call2), (call2, call1))              
          }
        } else {
          throw new IllegalStateException("Found incompatible expressions !! e1: " + call1 + " e2: " + call2)
        }
      }
    })    
    
    //Part (II) return the constraints. For equal calls, the constraints are just that their return values are equal, 
    //for others, it is an implication     
    //For equal class selectors, constraints are just that their return values are equal, for other's it is a bi-implication   
    val newctrs = product.foldLeft(Seq[Expr]())((acc,pair) => {
      val (call1,call2)= pair
      if(eqGraph.containsEdge(call1,call2)) {
               
        val BinaryOperator(r1@_,_,_) = call1
        val BinaryOperator(r2@_,_,_) = call2
        var preds = if(r1 != r2) Seq(Equals(r1,r2))
        			else Seq()
        
        //we need to add more constraints if  call1 and call2 are ADTcons
        if(InvariantUtil.isADTConstructor(call1)) {          
          
          val (lhs,_) = axiomatizeADTCons(call1,call2)                    
          val newLHS = lhs.filter(_ match {
            case BinaryOperator(Variable(lid),Variable(rid), _) => {
              //remove self equalities.
              if(lid == rid) false
              //TODO: remove the equalities between dummy ids. why is this not working ?
              //else if(TempIdFactory.isDummy(lid) || TempIdFactory.isDummy(rid)) false              
              else true
            }
            case e@_ => throw new IllegalStateException("Not an equality or Iff: "+e)
          })
          preds ++= newLHS
        }
        
        //Finally, removing predicates on ADTs
        acc ++ preds.filter((eq) => {
            val BinaryOperator(lhs, rhs, op) = eq
            (lhs.getType == Int32Type || lhs.getType == RealType || lhs.getType == BooleanType)
          }) 
      }      
      else if(neqSet.contains(pair)) {
        
        //adding single implication
        if(InvariantUtil.isCallExpr(call1)) {
                   
          val (ants,conseq) = axiomatizeCalls(call1,call2)
          //here, remove ADT equalities if any from the ant (because it was already implied)
          val intEqs = ants.filter((eq) => {
            val BinaryOperator(lhs, rhs, _) = eq
            (lhs.getType == Int32Type || lhs.getType == RealType || lhs.getType == BooleanType)
          }) 
          
          //return Args => rets
          acc :+ Or(Not(And(intEqs)),conseq)
        	
        } else {
          //adding bi-implication          
          val (lhs,rhs) = axiomatizeADTCons(call1,call2)
          val lhsExpr = And(lhs)
          acc :+ And(Or(Not(lhsExpr),rhs),Or(Not(rhs),lhsExpr))
        }        
      }        
      else acc
    })
    
    //for stats
    reporter.info("Number of SMT calls: "+smtCalls)    
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
   * TODO: Long Term: how can we handle functions in which arguments have template variables and template function names ??
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
   * The return value should be interpreted as a bidirectional implication
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
