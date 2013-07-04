package leon
package invariant

import z3.scala._
import purescala.DataStructures._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import solvers.{ Solver, TrivialSolver, TimeoutSolver }
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

class LinearSystemAnalyzer(ctrTracker : ConstraintTracker) {

  private val implicationSolver = new LinearImplicationSolver()

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
   * This function computes invariants belonging to the template.
   * The result is a mapping from function definitions to the corresponding invariants.
   */
  def solveForTemplates(uiSolver: UninterpretedZ3Solver): Option[Map[FunDef, Expr]] = {

    //traverse each of the functions and collect the constraints
    val nonLinearCtrs  = ctrTracker.getFuncs.foldLeft(Seq[Expr]())((acc, fd) => {

      val (btree,ptree) = ctrTracker.getVC(fd)      
      val ctr = generateCtrsForTree(btree, ptree, uiSolver)      
      (acc :+ ctr)
    })
    val nonLinearCtr = if(nonLinearCtrs.size == 1) nonLinearCtrs.first 
						else And(nonLinearCtrs)	

    //look for a solution of non-linear constraints. The constraint variables are all reals
    //println("Non linear constraints for this branch: " +nonLinearCtr)          
    val (res, model, unsatCore) = uiSolver.solveSATWithFunctionCalls(nonLinearCtr)
    if (res.isDefined && res.get == true) {
      //printing the model here for debugging
      //println("Model: "+model)
      //construct an invariant (and print the model)      
      val invs = ctrTracker.getFuncs.foldLeft(Seq[(FunDef,Expr)]())((acc, fd) => {
                           	
        val tempOption = TemplateFactory.getTemplate(fd)
      	if(!tempOption.isDefined)
      	    acc
      	else {
      		val template = tempOption.get
      		val tempvars = InvariantUtil.getTemplateVars(template)
      		val tempVarMap : Map[Expr,Expr] = tempvars.map((v) => {
      		  //println(v.id +" mapsto " + model(v.id))
      		  (v,model(v.id))
      		}).toMap

      		//do a simple post transform and replace the template vars by their values
      		val inv = simplePostTransform((tempExpr : Expr) => tempExpr match {
      		    case e@BinaryOperator(lhs,rhs,op) 
          			if ((e.isInstanceOf[Equals] || e.isInstanceOf[LessThan]
          		    || e.isInstanceOf[LessEquals] || e.isInstanceOf[GreaterThan]
          		    || e.isInstanceOf[GreaterEquals])) => { 
          		
            			val linearTemp = ctrTracker.exprToTemplate(tempExpr)
            		  val coeffMap = linearTemp.coeffTemplate.map((entry)=>{
            			val (term, coeffTemp) = entry
            			val coeffE = replace(tempVarMap,coeffTemp)
            		  val coeff = RealValuedExprInterpreter.evaluate(coeffE)
            			(term -> coeff)
          			})
          			val const = if(linearTemp.constTemplate.isDefined) 
          					Some(RealValuedExprInterpreter.evaluate(replace(tempVarMap,linearTemp.constTemplate.get)))
          		                    else None

          			val realValues : Seq[Expr] = coeffMap.values.toSeq ++ { if(const.isDefined) Seq(const.get) else Seq() }
          		
          			//the coefficients could be fractions ,so collect all the denominators
          			val getDenom = (t: Expr) => t match {
          			  case RealLiteral(num, denum) => denum
          			  case _ => 1
          			}

          			val denoms = realValues.foldLeft(Set[Int]())((acc, entry) => { acc + getDenom(entry) } )
          			//compute the LCM of the denominators (approx. LCM)
          			val lcm = denoms.foldLeft(1)((acc, d) => if (acc % d == 0) acc else acc * d)

          			//scale the numerator by lcm
          			val scaleNum = (t: Expr) => t match {
          			  case RealLiteral(num, denum) => IntLiteral(num * (lcm / denum))
          			  case IntLiteral(n) => IntLiteral(n * lcm)
          			  case _ => throw IllegalStateException("Coefficient not assigned to any value")
          			}
          			val intCoeffMap = coeffMap.map((entry) => (entry._1, scaleNum(entry._2)))
          			val intConst = if(const.isDefined) Some(scaleNum(const.get)) else None

          			val linearCtr = new LinearConstraint(linearTemp.op, intCoeffMap, intConst)
          			linearCtr.expr
      	  	  }
      		    case _ => tempExpr
      		})(template)	
      		acc :+ ((fd,inv))
        }	                        
      })
      Some(invs.toMap)
    } else {
      println("Constraint Unsat: " + unsatCore)
      None
    }
  }
  
  /**
   * Returns a set of non linear constraints for the given constraint tree
   */
  def generateCtrsForTree(bodyRoot: CtrNode, postRoot : CtrNode, uiSolver : UninterpretedZ3Solver) : Expr = {       
    
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
     * and "AND" as the join operation
     */
    def foldAND(trees : Iterable[CtrTree], pred: CtrTree => Expr): Expr = {
      var expr: Expr = tru
      trees.foreach((tree) => {        
        if (expr != fls) {
          val res = pred(tree)
          res match {
            case BooleanLiteral(false) => expr = fls;
            case BooleanLiteral(true) => ;
            case _ => {

              if (expr == tru) {
                expr = res
              } else expr = And(expr, res)
            }
          }
        }
      })
      expr
    } 

    /**
     * The overall flow:
     * Body --pipe---> post --pipe---> uifConstraintGen --pipe---> endPoint
     */        
    //this tree could have 2^n paths 
    def traverseBodyTree(tree: CtrTree, currentCtrs: Seq[LinearConstraint], currentUIFs: Set[Call], 
      currentTemps: Seq[LinearTemplate], auxCtrs : Seq[Expr]): Expr = {

      tree match {
        case n @ CtrNode(_) => {
          val newCtrs = currentCtrs ++ n.constraints
          val newTemps = currentTemps ++ n.templates
          val newUIFs = currentUIFs ++ n.uifs
          val newAuxs = auxCtrs ++ (n.boolCtrs.map(_.expr) ++ n.adtCtrs.map(_.expr))

          //recurse into children and collect all the constraints
          foldAND(n.Children, (child : CtrTree) => traverseBodyTree(child, newCtrs, newUIFs, newTemps, newAuxs))
        }
        case CtrLeaf() => {

          val pathexpr = constraintsToExpr(currentCtrs, currentUIFs, And(auxCtrs))
          val (res, model, unsatCore) = uiSolver.solveSATWithFunctionCalls(pathexpr)
          if (!res.isDefined || res.get == true) {

            //println("Body path expr: " + pathexpr)
            
            //pipe this to the post tree
            traversePostTree(postRoot, currentCtrs, currentTemps, auxCtrs, currentUIFs, Seq(), Seq(), Seq())                                      
          } else {
            //println("Found unsat path: " + pathExpr)
            tru
          }
        }
      }
    }
     
    //this tree could have 2^n paths
    def traversePostTree(tree: CtrTree, ants: Seq[LinearConstraint], antTemps: Seq[LinearTemplate],
      antAuxs: Seq[Expr], currUIFs: Set[Call], conseqs: Seq[LinearConstraint], 
      currTemps: Seq[LinearTemplate], currAuxs: Seq[Expr]): Expr = {
    						
      tree match {
        case n @ CtrNode(_) => {          
          val newcons = conseqs ++ n.constraints
          val newuifs = currUIFs ++ n.uifs 
          val newtemps = currTemps ++ n.templates
          val newAuxs = currAuxs ++ (n.boolCtrs.map(_.expr) ++ n.adtCtrs.map(_.expr))
          
          //recurse into children and collect all the constraints
          foldAND(n.Children, (child : CtrTree) => traversePostTree(child, ants, antTemps, antAuxs, 
            newuifs, newcons, newtemps, newAuxs)) 
        }
        case CtrLeaf() => {                 
          //pipe to the uif constraint generator
          uifsConstraintsGen(ants, antTemps, antAuxs, currUIFs, conseqs, currTemps, currAuxs)
        }
      }
    }
    
    /**
     * Eliminates the calls using the theory of uninterpreted functions
     * this could take 2^(n^2) time
     */
    def uifsConstraintsGen(ants: Seq[LinearConstraint], antTemps: Seq[LinearTemplate], antAuxs: Seq[Expr],
         calls: Set[Call], conseqs: Seq[LinearConstraint], conseqTemps: Seq[LinearTemplate], conseqAuxs: Seq[Expr]) : Expr = {
      
      def traverseTree(tree: CtrTree, 
         ants: Seq[LinearConstraint], antTemps: Seq[LinearTemplate], 
         conseqs: Seq[LinearConstraint], conseqTemps: Seq[LinearTemplate]): Expr = {
        
        tree match {
          case n @ CtrNode(_) => {
            val newants = ants ++ n.constraints
            //recurse into children            
            foldAND(n.Children, (child : CtrTree) => traverseTree(child, newants, antTemps, conseqs, conseqTemps))
          }
          case CtrLeaf() => {            
            //pipe to the end point that invokes the constraint solver
            endpoint(ants,antTemps,conseqs,conseqTemps)
          }
        }
      }

      val pathexpr = constraintsToExpr(ants ++ conseqs, calls, And(antAuxs ++ conseqAuxs))        
      println("Full-path: " + pathexpr)

      //if the path expression is unsatisfiable return true
      val (res, model, unsatCore) = uiSolver.solveSATWithFunctionCalls(pathexpr)
      if (res.isDefined && res.get == false) {
        tru            
      } else {
                    //println("All ctrs: "+ (ants ++ conseqs ++ calls ++ conseqTemps))                  
        val uifCtrs = constraintsForUIFs(calls.toSeq, pathexpr, uiSolver)
        
        val uifroot = if (!uifCtrs.isEmpty) {
        
          val uifCtr = And(uifCtrs)
          println("UIF constraints: " + uifCtr)        
          //push not inside
          val nnfExpr = InvariantUtil.TransformNot(uifCtr)        
          //create the root of the UIF tree
          //TODO: create a UIF tree once and for all and prune the paths while traversing
          val newnode = CtrNode()
          //add the nnfExpr as a DNF formulae
          ctrTracker.addConstraintRecur(nnfExpr, newnode)
          newnode

        } else CtrLeaf()
        //fls
        traverseTree(uifroot, ants, antTemps, conseqs, conseqTemps)  
      }      
    }

    /**
     * Endpoint of the pipeline. Invokes the actual constraint solver.
     */
    def endpoint(ants: Seq[LinearConstraint], antTemps: Seq[LinearTemplate],
      conseqs: Seq[LinearConstraint], conseqTemps: Seq[LinearTemplate]): Expr = {
      //here we are solving A^~(B)
      if (conseqs.isEmpty && conseqTemps.isEmpty) tru
      else {
        val implCtrs = implicationSolver.constraintsForUnsat(ants, antTemps, conseqs, conseqTemps, uiSolver)
        //println("Implication Constraints: "+implCtrs)
        implCtrs
      }
    }
        
    val nonLinearCtr = traverseBodyTree(bodyRoot, Seq(), Set(), Seq(), Seq())

    nonLinearCtr match {
      case BooleanLiteral(true) => throw IllegalStateException("Found no constraints")
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
  //TODO: Find ways to efficiently handle ADTs (the current solution is incomplete for efficiency)
  def constraintsForUIFs(calls: Seq[Call], precond: Expr, uisolver: UninterpretedZ3Solver) : Seq[Expr] = {
        
    //Part(I): Finding the set of all pairs of funcs that are implied by the precond
    var impliedGraph = new UndirectedGraph[Call]()
    var nimpliedSet = Set[(Call,Call)]()
    
    //compute the cartesian product of the calls and select the pairs having the same function symbol and also implied by the precond
    val vec = calls.toArray
    val size = calls.size
    var j = 0
    val product = vec.foldLeft(Set[(Call, Call)]())((acc, call) => {

      var pairs = Set[(Call, Call)]()
      for (i <- j + 1 until size) {
        val call2 = vec(i)
        if (call.fi.funDef == call2.fi.funDef)
          pairs ++= Set((call, call2))
      }
      j += 1
      acc ++ pairs
    })
    
    product.foreach((pair) => {
      val (call1,call2) = (pair._1,pair._2)
      if(!impliedGraph.BFSReach(call1, call2)){        
        if(!nimpliedSet.contains((call1, call2))){          
          val (ant,conseqs) = axiomatizeEquality(call1,call2)
         //check if equality follows from the preconds                   
          val (nImpRes,_,_) = uisolver.solveSATWithFunctionCalls(Not(Implies(precond,ant)))
          val (impRes,_,_) = uisolver.solveSATWithFunctionCalls(And(precond,ant))
          (nImpRes,impRes) match{
            case (Some(false),_) => {
             //here the argument equality follows from the precondition
              impliedGraph.addEdge(call1, call2)              
            }
            case (_,Some(false)) => {
              //here the arg. equality will never be implied by the precond (unless the precond becomes false). 
              //Therefore we can drop this constraint           
              ;              
            }
            case _ => {
              //here the arg. equality does not follow from the precondition but may be implied by instantiation of the templates                            

              //An incomplete efficiency heuristic
              //consider the ADT equalities in Ants alone. If that is not implied by precond then drop this call (incompletely assume
              // that templates cannot make them equal)
              val eqs = ant match{
                case And(args) => args
                case Equals(_,_) => Seq(ant)
                case _ => throw IllegalStateException("Not a conjunction of equalities"+ant)
              }
              val adtEqs = eqs.filter((eq) => { 
                val Equals(lhs,rhs) = eq
                (lhs.getType != Int32Type && lhs.getType != RealType)                
              })
              val (adtImp,_,_) = uisolver.solveSATWithFunctionCalls(Not(Implies(precond,And(eqs))))
              if(adtImp.isDefined && adtImp.get == true){
                //here the implication need not necessarily hold therefore we consider that it can never 
                //hold (assuming that the templates do not affect ADTs values thtough integers)
                ;
              }
              else{
                nimpliedSet ++= Set((call1,call2),(call2,call1))                       
                //TODO: consider the following optimization :
                //take the model found in this case. If the instantiation of the template does not satisfy the model
                //then may be it could imply the equality. So, we could try this case later. 
              }
            }
          }                  
        }                     
      }
    })    
    
    //Part (II) return the constraints. For each implied call, the constraints are just that their return values are equal.
    //For other calls the constraints are full implication    
    val newctrs = product.foldLeft(Seq[Expr]())((acc,pair) => {
      val (call1,call2)= pair
      if(impliedGraph.containsEdge(call1,call2)) {
        acc :+ Equals(call1.retexpr,call2.retexpr)
      }
      else if(nimpliedSet.contains(pair)) {
        val (ant,conseq) = axiomatizeEquality(call1,call2)
        acc :+ Or(Not(ant),conseq)
      }        
      else acc
    })
    newctrs
  }

  /**
   * This procedure generates constraints for the calls to be equal
   * TODO: how can we handle functions in which arguments have templates and templated functions ??
   */
  def axiomatizeEquality(call1: Call, call2: Call): (Expr, Expr) = {
    val v1 = call1.retexpr
    val fi1 = call1.fi
    val v2 = call2.retexpr
    val fi2 = call2.fi

    val ants = (fi1.args.zip(fi2.args)).foldLeft(Seq[Expr]())((acc, pair) => {
      val (arg1, arg2) = pair
      acc :+ Equals(arg1, arg2)
    })
    val conseq = Equals(v1, v2)
    (And(ants), conseq)
  } 
  
}
