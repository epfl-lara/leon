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
      val ctr = generateCtrsForTree(btree, ptree, uiSolver, selector, false)      
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
  def solveForTemplatesIncr(uiSolver: SimpleSolverAPI): Option[Map[FunDef, Expr]] = {

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
        println("Choosing constraints without calls")
        ctr = generateCtrsForTree(btree, ptree, uiSolver, noRecursiveCallSelector(fd), true)
        println("Found Some: " + (ctr != tru))
      }
            
      if (ctr == tru) {        
        //this may get into an infinite while loop in rare scenarios
        //TODO: critical : how to fix this ??
        //TODO: what if all the paths in the program are infeasible ? may be we should time out after sometime and have some random assignment
        //of values to the terms.
        println("Randomly choosing constraints ...")
        while (ctr == tru) {
          println("Looping...")
          ctr = generateCtrsForTree(btree, ptree, uiSolver, randomSelector, false)
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
    
    val solution = recSolveForTemplatesIncr(solverWithCtrs, uiSolver, funcExprs)
    solverWithCtrs.free()
    solution
  }  
  
  def recSolveForTemplatesIncr(solverWithCtrs: UIFZ3Solver, uiSolver: SimpleSolverAPI, funcExprs: Map[FunDef, Expr])
  			: Option[Map[FunDef, Expr]] = {

    val funcs = funcExprs.keys

    println("solving...")       
    val t1 = System.currentTimeMillis()

    //println("Assertions: \n"+solverWithCtrs.ctrsToString)               
    /*FileCountGUID.fileCount += 1
    val pwr = new PrintWriter("z3formula-"+FileCountGUID.fileCount+".smt")    
    pwr.println(solverWithCtrs.ctrsToString)
    pwr.flush()
    pwr.close()*/
    
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
        val compModel = completeModel(model, TemplateIdFactory.getTemplateIds)
        
        //For debugging: printing the candidate invariants found at this step
        println("candidate Invariants")
        val candInvs = getAllInvariants(compModel)
        candInvs.foreach((entry) => println(entry._1.id + "-->" + entry._2))

        //check if 'inv' is a 'sufficiently strong' invariant by looking for a counter-example. 
        //if one exists find a path (in each tree) that results in the counter-example and add farkas' 
        //constraints for the path to the constraints to be solved        
        val tempVarMap: Map[Expr, Expr] = compModel.map((elem) => (elem._1.toVariable,elem._2)).toMap

       //val wr = new PrintWriter(new File("formula-dump.txt"))
        val newctrs = funcs.foldLeft(Seq[Expr]())((acc, fd) => {
          
          val instVC = simplifyArithmetic(instantiateTemplate(funcExprs(fd), tempVarMap))

          //For debugging                    
          /*wr.println("Function name: " + fd.id)
          wr.println("Formula expr: ")
          InvariantUtil.PrintWithIndentation(wr, InvariantUtil.unFlatten(cande))*/

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
              println("Function: " + fd.id + "--Found candidate invariant is not a real invariant! ")//+solEval.getInternalModel)

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
              val newctr = generateCtrsForTree(btree, ptree, uiSolver, satChooser, true)
              if(newctr == tru)
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
        if(newctrs.isEmpty) {
          //yes, hurray
          //print some statistics 
          reporter.info("- Number of explored paths (of the DAG) in this unroll step: "+exploredPaths)
           
          Some(getAllInvariants(compModel))          
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
  
  /**
   * Returns a set of non linear constraints for the given constraint tree.
   * This is parametrized by a selector function that decides which paths to consider. 
   */
  def generateCtrsForTree(bodyRoot: CtrNode, postRoot : CtrNode, 
      uiSolver : SimpleSolverAPI, selector : (CtrNode, Iterable[CtrTree], Int) => Iterable[CtrTree],
      exploreOnePath : Boolean) : Expr = {       
    
    /**
     * A utility function that converts a constraint + calls into a expression.
     * Note: adds the uifs in conjunction to the ctrs
     */    
    def constraintsToExpr(ctrs: Seq[LinearConstraint], calls: Set[Call], auxExpr: Expr): Expr = {
      val pathExpr = And(ctrs.foldLeft(Seq[Expr]())((acc, ctr) => (acc :+ ctr.expr)))
      val uifExpr = And(calls.map((call) => Equals(call.retexpr,call.fi)).toSeq)
      And(Seq(pathExpr, uifExpr, auxExpr))
    }    

    /**
     * A helper function that composes a sequence of CtrTrees using the provided operation 
     * and "AND" as the join operation.     
     * TODO: Maintenance Issue: The following code is imperative
     */
    def foldAND(parent: CtrNode, childTrees : Iterable[CtrTree], pred: CtrTree => Expr, depth: Int): Expr = {
      
      //get the children that need to be traversed
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
    //this tree could have 2^n paths 
    def traverseBodyTree(tree: CtrTree, 
        currentCtrs: Seq[LinearConstraint], 
        currentUIFs: Set[Call], 
        currentTemps: Seq[LinearTemplate],
        classSelectors : Seq[Expr],
        auxCtrs : Seq[Expr],         
        depth : Int): Expr = {

      tree match {
        case n @ CtrNode(_) => {
          //println("Traversing Body Tree")
          val newCtrs = currentCtrs ++ n.constraints
          val newTemps = currentTemps ++ n.templates
          val newUIFs = currentUIFs ++ n.uifs
          val classSels = classSelectors ++ n.adtCtrs.collect{ case adtctr@_ if adtctr.sel.isDefined => adtctr.sel.get }          
          val newAuxs = (auxCtrs ++ n.boolCtrs.map(_.expr)) ++ n.adtCtrs.collect{ case ac@_ if !ac.sel.isDefined => ac.expr }

          //recurse into children and collect all the constraints
          foldAND(n, n.Children, (child : CtrTree) => traverseBodyTree(child, newCtrs, newUIFs, newTemps, classSels, newAuxs, depth + 1), depth)
        }
        case CtrLeaf() => {

          val pathexpr = constraintsToExpr(currentCtrs, currentUIFs, And(auxCtrs))
          val (res, model) = uiSolver.solveSAT(pathexpr)
          if (!res.isDefined || res.get == true) {

            //println("Body path expr: " + pathexpr)
            
            //pipe this to the post tree           
            traversePostTree(postRoot, currentCtrs, currentTemps, auxCtrs, currentUIFs, classSelectors, Seq(), Seq(), Seq(), depth + 1)                                      
          } else {
            //println("Found unsat path: " + pathExpr)
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
        classSels : Seq[Expr],
        conseqs: Seq[LinearConstraint], 
        currTemps: Seq[LinearTemplate],        
        currAuxs: Seq[Expr], depth: Int): Expr = {
          						
      tree match {
        case n @ CtrNode(_) => {          
          //println("Traversing Post Tree")
          val newcons = conseqs ++ n.constraints
          val newuifs = currUIFs ++ n.uifs 
          val newtemps = currTemps ++ n.templates
          val newSels = classSels ++ n.adtCtrs.collect{ case adtctr@_ if adtctr.sel.isDefined => adtctr.sel.get } 
          val newAuxs = currAuxs ++ (n.boolCtrs.map(_.expr) ++ n.adtCtrs.collect{ case adtctr@_ if !adtctr.sel.isDefined => adtctr.expr })
          
          //recurse into children and collect all the constraints
          foldAND(n, n.Children, (child : CtrTree) => traversePostTree(child, ants, antTemps, antAuxs, 
            newuifs, newSels, newcons, newtemps, newAuxs, depth + 1), depth) 
        }
        case CtrLeaf() => {                 

          //println("path after post traversal: "+constraintsToExpr(ants ++ conseqs, currUIFs, And(antAuxs ++ currAuxs)))                   
          //pipe to the uif constraint generator
          uifsConstraintsGen(ants, antTemps, antAuxs, currUIFs, classSels, conseqs, currTemps, currAuxs, depth + 1)
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
        classSels: Seq[Expr], 
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
            val newants = ants ++ n.constraints
            //recurse into children            
            foldAND(n, n.Children, (child : CtrTree) => traverseTree(child, newants, antTemps, conseqs, conseqTemps, dep + 1), dep)
          }
          case CtrLeaf() => {            
            //pipe to the end point that invokes the constraint solver
            endpoint(ants,antTemps,conseqs,conseqTemps)
          }
        }
      }

      val pathexpr = constraintsToExpr(ants ++ conseqs, calls, And(classSels ++ antAuxs ++ conseqAuxs))              

      //if the path expression is unsatisfiable return true
      val (res, model) = uiSolver.solveSAT(pathexpr)
      if (res.isDefined && res.get == false) {
        tru            
      } else {
        val uifexprs = calls.map((call) => Equals(call.retexpr,call.fi)).toSeq
        //for debugging
        //println("Full-path: " + simplifyArithmetic(pathexpr))
        //println("All ctrs: "+ (ants ++ conseqs ++ calls ++ conseqTemps))                             
          val pathexprs = (ants ++ antTemps ++ conseqs ++ conseqTemps).map(_.template)
          val plainFormula = And(antAuxs ++ conseqAuxs ++ classSels ++ uifexprs ++  pathexprs)
          val formula = simplifyArithmetic(plainFormula)          
          /*val wr = new PrintWriter(new File("full-path-"+formula.hashCode()+".txt"))
          ExpressionTransformer.PrintWithIndentation(wr, formula)
          wr.flush()
          wr.close()*/
          println("Full-path: " + formula)
          
        //println("Starting Constraint generation")
        val uifCtrs = constraintsForUIFs(uifexprs ++ classSels, pathexpr, uiSolver)
        //println("Generated UIF Constraints")
        
        val uifroot = if (!uifCtrs.isEmpty) {
        
          val uifCtr = And(uifCtrs)
          println("UIF constraints: " + uifCtr)        
          //push not inside
          val nnfExpr = ExpressionTransformer.TransformNot(uifCtr)        
          //create the root of the UIF tree
          //TODO: create a UIF tree once and for all and prune the paths while traversing
          val newnode = CtrNode()
          //add the nnfExpr as a DNF formulae
          ctrTracker.addConstraintRecur(nnfExpr, newnode)
          newnode

        } else CtrLeaf()
        //fls
        traverseTree(uifroot, ants, antTemps, conseqs, conseqTemps, depth)  
      }      
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
      else {
        exploredPaths += 1
                
        println("Final Path Constraints: "+And((ants ++ antTemps ++ conseqs ++ conseqTemps).map(_.template)))
        val implCtrs = implicationSolver.constraintsForUnsat(ants, antTemps, conseqs, conseqTemps, uiSolver)
        
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
  
  //convert the theory formula into linear arithmetic formula
  //TODO: Fix the current incomplete way of handling ADTs
  //TODO: For efficiency, consider only functions with integer return type, also consider CaseClassSelectors and TupleSelectors
  //TODO: one idea: use the dependence chains in the formulas to identify what to assertionze and what can never be implied
  // by solvign for the templates
  def constraintsForUIFs(calls: Seq[Expr], precond: Expr, uisolver: SimpleSolverAPI) : Seq[Expr] = {
        
    //Part(I): Finding the set of all pairs of calls (or expressions) that are implied by the precond
    var eqGraph = new UndirectedGraph[Expr]() //an equality graph
    var neqSet = Set[(Expr,Expr)]()
    
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
        /*if (call.fi.funDef == call2.fi.funDef)
          pairs ++= Set((call, call2))*/
      }
      j += 1
      acc ++ pairs
    })
    
    def isImplied(cond: Expr): TVL.Value = {
      
      //check if the cond follows from the preconds                   
      val (nImpRes, _) = uisolver.solveSAT(Not(Implies(precond, cond)))
      val (impRes, _) = uisolver.solveSAT(And(precond, cond))
      (nImpRes, impRes) match {
        case (Some(false), _) => TVL.TRUE                     
        case (_, Some(false)) => TVL.FALSE                    
        case _ => TVL.MAYBE            
      }
    }

    /**
     * Requires 'e' to be a cojunction of equalities.
     * Returns a set of ADT equalities in the input expression
     */
    def ADTequalities(e: Expr): Seq[Expr] = {
      (e match {
        case And(args) => args
        case Equals(_, _) => Seq(e)
        case _ => throw IllegalStateException("Not a conjunction of equalities" + e)

      }).filter((eq) => {

        val Equals(lhs, rhs) = eq
        (lhs.getType != Int32Type && lhs.getType != RealType)

      })
    }
    
    product.foreach((pair) => {
      val (call1,call2) = (pair._1,pair._2)      
      if(!eqGraph.BFSReach(call1, call2)){        
        if(!neqSet.contains((call1, call2))){    
          
          if(InvariantUtil.isCallExpr(call1)) {
            val (ant,conseq) =  axiomatizeCalls(call1,call2)
            val tv = isImplied(ant)
            if (tv == TVL.FALSE) {
              //here the arg. equality will never be implied by the precond (unless the precond becomes false). 
              //Therefore we can drop this constraint           
              ;
            } else if (tv == TVL.TRUE) {
              //here the argument equality follows from the precondition
              eqGraph.addEdge(call1, call2)
            } else {
              //here the argument equality does not follow from the precondition but may be implied by instantiation of the templates
              //TODO: try some optimizations here, put the ideas here
              //TODO: consider the following optimization :
              //take the model found in this case. If the instantiation of the template does not satisfy the model
              //then may be it could imply the equality. So, we could try this case later.              

              //An incomplete efficiency heuristic
              //If the adt equalities in ant is not implied by precond then drop this call (incompletely assume
              // that templates cannot make them equal), this is true when the adts are inputs
              val adtEqs = ADTequalities(ant)
              val (adtImp,_) = uisolver.solveSAT(Not(Implies(precond,And(adtEqs))))
              if(adtImp.isDefined && adtImp.get == true){
                //here the implication need not necessarily hold therefore we consider that it can never 
                //hold (assuming that the templates do not affect ADTs values through integers)
                ;
              }
              else{              
            	neqSet ++= Set((call1, call2), (call2, call1))
              }
            }                              
          } /*else if(InvariantUtil.isSelector(call1)){
            val (lhs, rhs) = axiomatizeSelectors(call1,call2)
            
            //the two expressions are equal (or notequal) either if lhs are equal (or notequal) or if rhs are equal (or notequal)            
            val tv1 = isImplied(lhs)
            val tv2 = if(tv1 == TVL.MAYBE) isImplied(rhs)
            		  else TVL.MAYBE
            //note that since the formula is consistent, tv1 and tv2 must compatible i.e, one cannot be true and other false
            if(tv1 == TVL.TRUE || tv2 == TVL.TRUE){
              eqGraph.addEdge(call1, call2)
              
            } else if(tv1 == TVL.FALSE || tv2 == TVL.FALSE) {
              ;  //drop this
            } else {
              //here both are maybe
              neqSet ++= Set((call1, call2), (call2, call1))
            }            
          } */else {
            throw new IllegalStateException("Found incompatible expressions !!")
          }  
                    
        }                     
      }
    })    
    
    //Part (II) return the constraints. For equal calls, the constraints are just that their return values are equal, 
    //for others, it is an implication     
    //For equal class selectors, constraints are just that their return values are equal, for other's it is a bi-implication   
    val newctrs = product.foldLeft(Seq[Expr]())((acc,pair) => {
      val (call1,call2)= pair
      if(eqGraph.containsEdge(call1,call2)) {
        
        val Equals(r1@_,_) = call1
        val Equals(r2@_,_) = call2
        acc :+ Equals(r1,r2)        
      }
      else if(neqSet.contains(pair)) {
        
        //adding single implication
        if(InvariantUtil.isCallExpr(call1)) {
                   
          val (ant,conseq) = axiomatizeCalls(call1,call2)
          //here, remove ADT equalities if any from the ant (because it was already implied)
          val intEqs = (ant match {
            case And(args) => args
            case Equals(_, _) => Seq(ant)

          }).filterNot((eq) => {

            val Equals(lhs, rhs) = eq
            (lhs.getType == Int32Type || lhs.getType == RealType)

          }) 
          
          //return Args => rets
          acc :+ Or(Not(And(intEqs)),conseq)
        	
        } else {
          //adding bi-implication          
          val (lhs,rhs) = axiomatizeSelectors(call1,call2)
          acc :+ And(Or(Not(lhs),rhs),Or(Not(rhs),lhs))
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
      case (Equals(_, CaseClassSelector(cd1, _, id1)), Equals(_, CaseClassSelector(cd2, _, id2))) if (cd1 == cd2 && id1 == id2) => true
      case (Equals(_, TupleSelect(e1, i1)), Equals(_, TupleSelect(e2, i2))) if (e1.getType == e2.getType && i1 == i2) => true
      case _ => false
    }
  }

  /**
   * This procedure generates constraints for the calls to be equal
   * TODO: how can we handle functions in which arguments have template variables and template function names ??
   */
  def axiomatizeCalls(call1: Expr, call2:  Expr): (Expr, Expr) = {    
    
    val Equals(v1,fi1@FunctionInvocation(_,_)) = call1
    val Equals(v2,fi2@FunctionInvocation(_,_)) = call2
    
    val ants = (fi1.args.zip(fi2.args)).foldLeft(Seq[Expr]())((acc, pair) => {
      val (arg1, arg2) = pair
      acc :+ Equals(arg1, arg2)
    })
    val conseq = Equals(v1, v2)
    (And(ants), conseq)
  }   
  
  /**
   * The return value should be interpreted as a bidirectional implication
   */
  def axiomatizeSelectors(sel1: Expr, sel2:  Expr): (Expr, Expr) = {    

    sel1 match {
      case Equals(r1@Variable(_),CaseClassSelector(_,arg1,_)) => {
        val Equals(r2@Variable(_),CaseClassSelector(_,arg2,_)) = sel2
        (Equals(arg1,arg2), Equals(r1,r2))
      } 
      case Equals(r1@Variable(_),TupleSelect(arg1,_)) => {
        val Equals(r2@Variable(_),TupleSelect(arg2,_)) = sel2
        (Equals(arg1,arg2), Equals(r1,r2))
      }
    }    
  }
  
}
