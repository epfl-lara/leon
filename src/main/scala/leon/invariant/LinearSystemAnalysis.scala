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

//Class representing linear templates which is a constraint of the form a1*v1 + a2*v2 + .. + an*vn + a0 <= 0 or = 0 where a_i's can be free vars
case class LinearTemplate(val template: Expr, val coeffTemplate: Map[Expr, Expr with Terminal], val constTemplate: Option[Expr with Terminal]) {
  def coeffEntryToString(coeffEntry: (Expr, Expr with Terminal)): String = {
    val (e, i) = coeffEntry
    i match {
      case IntLiteral(1) => e.toString
      case IntLiteral(-1) => "-" + e.toString
      case IntLiteral(v) => v + e.toString
      case _ => i + " * " + e.toString
    }
  }

  override def toString(): String = {
    val (head :: tail) = coeffTemplate.toList

    val constStr = tail.foldLeft(coeffEntryToString(head))((str, pair) => {

      val termStr = coeffEntryToString(pair)
      (str + " + " + termStr)
    }) +
      (if (constTemplate.isDefined) " + " + constTemplate.get.toString
      else "") +
      (template match {
        case t: Equals => " = "
        case t: LessThan => " < "
        case t: GreaterThan => " > "
        case t: LessEquals => " <= "
        case t: GreaterEquals => " >= "
      }) + "0"

    constStr //+ " ActualExpr: "+ expr
  }

  override def hashCode(): Int = {
    template.hashCode()
  }

  override def equals(obj: Any): Boolean = obj match {
    case lit: LinearTemplate => {
      if (!lit.template.equals(this.template)) {
        //println(lit.template + " and " + this.template+ " are not equal ")
        false
      } else true
    }
    case _ => false
  }
}

//class representing a linear constraint. This is a linear template wherein the coefficients are constants
case class LinearConstraint(val expr: Expr, val coeffMap: Map[Expr, IntLiteral], val constant: Option[IntLiteral])
  extends LinearTemplate(expr, coeffMap, constant) {
}

//A DAG that represents a DNF formula. Every path in the DAG corresponds to a disjunct
//TODO: Maintenance Issue: Fix this entire portion of code that manipulates the tree
abstract class CtrTree
case class CtrLeaf() extends CtrTree
case class CtrNode(val blockingId: Identifier) extends CtrTree {

  var constraints = Set[LinearConstraint]()
  //UI function calls
  var uifs = Set[Expr]()
  private var children = Set[CtrTree](CtrLeaf())

  def Children: Set[CtrTree] = children

  def copyChildren(newnode: CtrNode) = {
    newnode.children = this.children
  }

  def removeAllChildren() = {
    this.children = Set(CtrLeaf())
  }

  def addChildren(child: CtrNode) = {
    if (children.size == 1 && children.first == CtrLeaf())
      children = Set[CtrTree](child)
    else
      children += child
  }

  override def toString(): String = {
    var str = "Id: " + blockingId + " Constriants: " + constraints + " children: \n"
    children.foldLeft(str)((g: String, node: CtrTree) => { g + node.toString })
  }
}

class ConstraintTracker(fundef : FunDef) {

  private val implicationSolver = new LinearImplicationSolver()
  //this is a mutable map (used for efficiency)
  //private var treeNodeMap = collection.mutable.Map[Identifier, CtrNode]()
  
  //verification conditions for each procedure that may have templates.
  //Each verification condition is an implication where the antecedent and the consequent are represented as DNF trees.
  private var templatedVCs = Map[FunDef,(CtrNode,CtrNode,collection.mutable.Map[Identifier, CtrNode])]()
  
  //some identifiers representing body start and post start
  val bstart = FreshIdentifier("bstart")
  val pstart = FreshIdentifier("pstart")
  
  /*//This would be set while constraints are added
  //body and post are DNF formulas and hence are represented using trees
  private var bodyRoot = CtrNode()
  private var postRoot = CtrNode()    
  */
  //some constants
  private val zero = IntLiteral(0)
  private val one = IntLiteral(1)
  private val mone =IntLiteral(-1)   
  
  def addConstraintRecur(inexpr: Expr, parentNode : CtrNode, nodeMap: collection.mutable.Map[Identifier, CtrNode]) : Unit = {
    //returns the children nodes classified into real and dummy children. The first set is the real set and the second is the dummy set
    def addCtrOrBlkLiteral(ie: Expr, newChild: Boolean): (Set[CtrNode], Set[CtrNode]) = {
      ie match {
        case Or(subexprs) => {
          val validSubExprs = subexprs.collect((sube) => sube match {
            case _ if (sube match {
              //cases to be ignored              
              case Not(Variable(childId)) => false //need not take this into consideration now
              case _ => true
            }) => sube
          })
          if (!validSubExprs.isEmpty) {
            val createChild = if (validSubExprs.size > 1) true else false
            validSubExprs.foldLeft((Set[CtrNode](), Set[CtrNode]()))((acc, sube) => {
              val (real, dummy) = acc
              val (real2, dummy2) = addCtrOrBlkLiteral(sube, createChild)
              (real ++ real2, dummy ++ dummy2)
            })
          } else (Set(), Set())
        }
        case And(subexprs) => {
          subexprs.foldLeft((Set[CtrNode](), Set[CtrNode]()))((acc, sube) => {
            val (real, dummy) = acc
            val (real2, dummy2) = addCtrOrBlkLiteral(sube, false)
            (real ++ real2, dummy ++ dummy2)
          })
        }

        case Variable(childId) => {
          //checking for blocking literal
          if (isBlockingId(childId)) {
            (Set(createOrLookupId(parentNode, childId, nodeMap)), Set())
          } else
            throw IllegalStateException("Encountered a variable that is not a blocking id: " + childId)
        }
        case Iff(lhs, rhs) => {
          //lhs corresponds to a blocking id in this case
          lhs match {
            case Variable(childId) if (isBlockingId(childId)) => {
              val childNode = createOrLookupId(parentNode, childId, nodeMap)              
              //recursively add the rhs to the childNode
              addConstraintRecur(rhs,childNode, nodeMap)              
              (Set(childNode), Set())
            }
            case _ => throw IllegalStateException("Iff block --- encountered something that is not a blocking id: " + lhs)
          }

        }
        case _ => {
          val node = if (newChild) createOrLookupId(parentNode, FreshIdentifier("dummy", true), nodeMap)
        		  	 else parentNode
          val ctr = exprToConstraint(ie)
          node.constraints += ctr
          if (newChild) (Set(), Set(node)) else (Set(), Set())
        }
      }
    }
    val (realChildren, dummyChildren) = addCtrOrBlkLiteral(inexpr, false)

    //now merge dummy children with the ctrnode itself.
    //the following code is slightly nasty and with side effects
    val newParentNode = if (!dummyChildren.isEmpty) {
      val newnode = CtrNode(parentNode.blockingId)
      parentNode.copyChildren(newnode)
      parentNode.removeAllChildren()
      dummyChildren.foreach((child) => { child.addChildren(newnode); parentNode.addChildren(child) })
      nodeMap.update(parentNode.blockingId, newnode)
      newnode
    } else parentNode

    realChildren.foreach(newParentNode.addChildren(_))
  }
  
  def createOrLookupId(parentNode: CtrNode, childId: Identifier, nodeMap: collection.mutable.Map[Identifier, CtrNode]): CtrNode = {
    var childNode = nodeMap.getOrElse(childId, {
      val node = CtrNode(childId)
      nodeMap += (childId -> node)
      node
    })
    childNode
  }
  
  //some utility methods
  def isBlockingId(id: Identifier): Boolean = {
    if (id.name.startsWith("b")) true else false
  }

  def isStartId(id: Identifier): Boolean = {
    if (id.name.contains("start")) true else false
  }
  
  def getTemplatedVC(fdef: FunDef) : (CtrNode,CtrNode,collection.mutable.Map[Identifier, CtrNode]) ={
    templatedVCs.getOrElse(fdef, {
      //initialize body and post roots
      val newentry = (CtrNode(bstart),CtrNode(pstart),collection.mutable.Map[Identifier, CtrNode]())
      templatedVCs += (fdef -> newentry)
      newentry
    })    
  }

  def addBodyConstraints(fdef: FunDef, body: Seq[Expr]) = {
    val (bodyRoot,postRoot,nodeMap) = getTemplatedVC(fdef)    
    body.map(addConstraint(_, bodyRoot, postRoot, nodeMap, true))       
  }

  def addPostConstraints(fdef: FunDef, post: Seq[Expr]) = {
    val (bodyRoot,postRoot,nodeMap) = getTemplatedVC(fdef)
    post.map(addConstraint(_, bodyRoot, postRoot, nodeMap, false))    
  }

  def addConstraint(e: Expr, bodyRoot: CtrNode, postRoot: CtrNode, nodeMap: collection.mutable.Map[Identifier, CtrNode], isBody: Boolean) = {
    //apply negated normal form here
    val nnfExpr = TransformNot(e)
    //println("Expression after Not transformation: "+nnfExpr)
    val (id, innerExpr) = parseGuardedExpr(nnfExpr)

    //get the node corresponding to the id
    val ctrnode = nodeMap.getOrElse(id, {
      val node = if(isStartId(id)){
        if(isBody) bodyRoot
        else postRoot
      }
      else CtrNode(id)
      nodeMap += (id -> node)
      node
    })

    //flatten function returns a newexpresion without function symbols and a set of newly created equalities
    val (flatExpr,calls,newConjuncts) = FlattenFunction(innerExpr)

    //add the new conjuncts to the bodyRoot if we are in post
    if (!isBody) {
      if (!calls.isEmpty) {
        bodyRoot.uifs ++= calls
      }
      if (!newConjuncts.isEmpty) {
        addConstraintRecur(And(newConjuncts.toSeq), bodyRoot, nodeMap)
      }      
      //add the current expression to node given by the id
      addConstraintRecur(flatExpr, ctrnode, nodeMap)
    } else {
      ctrnode.uifs ++= calls
      val augExpr = And(flatExpr, And(newConjuncts.toSeq))
      //add the current expression to node given by the id
      addConstraintRecur(augExpr, ctrnode, nodeMap)
    }    
  }
  
  def parseGuardedExpr(e: Expr): (Identifier, Expr) = {
    e match {
      case Or(Not(Variable(id)) :: tail) => {
        tail match {
          case expr :: Nil => (id, expr)
          case expr :: tail2 => {
            //this corresponds to a disjunction
            (id, Or(tail))
          }
          case _ => throw IllegalStateException("Not in expected format: " + tail)
        }
      }
      case _ => throw IllegalStateException("Not a guarded expression: " + e)
    }
  }

  //the expr is required to be linear, if not, an exception would be thrown
  //for now some of the constructs are not handled
  def exprToConstraint(expr: Expr): LinearConstraint = {
    var coeffMap = Map[Expr, IntLiteral]()
    var constant: Option[IntLiteral] = None
   
    def genConstraint(e: Expr): Option[Expr] = {
      e match {
        case IntLiteral(v) => {
          constant = Some(IntLiteral(v))
          None
        }
        case Plus(e1, e2) => {
          if (e1.isInstanceOf[IntLiteral] && e2.isInstanceOf[IntLiteral])
            throw IllegalStateException("sum of two constants, not in canonical form: " + e)

          val r1 = genConstraint(e1)
          if (r1.isDefined) {
            //here the coefficient is 1
            coeffMap += (r1.get -> one)
          }
          val r2 = genConstraint(e2)
          if (r2.isDefined)
            coeffMap += (r2.get -> one)

          None
        }
        case Times(e1, e2) => {
          if (e1.isInstanceOf[IntLiteral] && e2.isInstanceOf[IntLiteral])
            throw IllegalStateException("product of two constants, not in canonical form: " + e)

          /*else if (!e1.isInstanceOf[IntLiteral] && !e2.isInstanceOf[IntLiteral])
            throw IllegalStateException("nonlinear expression: " + e)*/
          /*else {
            val (coeff, cvar) = e1 match {
              case IntLiteral(v) => (v, e2)
              case _ => {
                val IntLiteral(v) = e2
                (v, e1)
              }
            }*/
          val IntLiteral(v) = e1
          val (coeff, cvar) = (v, e2)

          val r = genConstraint(cvar)
          if (!r.isDefined)
            throw IllegalStateException("Multiplicand not a constraint variable: " + cvar)
          else {
            //add to mapping
            coeffMap += (r.get -> IntLiteral(coeff))
          }
          None
        }
        case v @ Variable(id) => {
          /*//this is a hack (store the result variable)
          if (id.name.equals("result") && !resultVar.isDefined)
            resultVar = Some(v)*/

          Some(v)
        }
        case FunctionInvocation(fdef, args) => Some(e)
        case BinaryOperator(e1, e2, op) => {

          /*if (!e.isInstanceOf[Equals] && !e.isInstanceOf[LessThan] && !e.isInstanceOf[LessEquals]
            && !e.isInstanceOf[GreaterThan] && !e.isInstanceOf[GreaterEquals])
            throw IllegalStateException("Relation is not linear: " + e)
          else {*/
          if (e1.isInstanceOf[IntLiteral] && e2.isInstanceOf[IntLiteral])
            throw IllegalStateException("relation on two integers, not in canonical form: " + e)

          e2 match {
            case IntLiteral(0) => {
              val r = genConstraint(e1)
              if (r.isDefined) {
                //here the coefficient is 1
                coeffMap += (r.get -> one)
              }
              None
            }
            case _ => throw IllegalStateException("Not in canonical form: " + e)
          }
        }
        case _ => {
          throw IllegalStateException("Ecountered unhandled term in the expression: " + e)
        }
      } //end of match e
    } //end of genConstraint      

    val linearExpr = MakeLinear(expr)
    if (!genConstraint(linearExpr).isDefined) {
      LinearConstraint(linearExpr, coeffMap, constant)
    } else
      throw IllegalStateException("Expression not a linear relation: " + expr)
  }

  /**
   * This method may have to do all sorts of transformation to make the expressions linear constraints.
   * This assumes that the input expression is an atomic predicate (i.e, without and, or and nots)
   * This is subjected to constant modification.
   */
  def MakeLinear(atom: Expr): Expr = {

    //pushes the minus inside the arithmetic terms
    def PushMinus(inExpr: Expr): Expr = {
      require(inExpr.getType == Int32Type)

      inExpr match {
        case IntLiteral(v) => IntLiteral(-v)
        case t: Terminal => Times(mone, t)
        case fi @ FunctionInvocation(fdef, args) => Times(mone, fi)
        case UMinus(e1) => e1
        case Minus(e1, e2) => Plus(PushMinus(e1), e2)
        case Plus(e1, e2) => Plus(PushMinus(e1), PushMinus(e2))
        case Times(e1, e2) => {
          //here push the minus in to the coefficient if possible
          e1 match {
            case IntLiteral(v) => Times(PushMinus(e1), e2)
            case _ => Times(e1, PushMinus(e2))
          }
        }
        case _ => throw NotImplementedException("PushMinus -- Operators not yet handled: " + inExpr)
      }
    }

    //we assume that PushMinus has already been invoke on the expression
    def PushTimes(c: Int, ine: Expr): Expr = {
      require(ine.getType == Int32Type)

      ine match {
        case IntLiteral(v) => IntLiteral(c * v)
        case t: Terminal => Times(IntLiteral(c), t)
        case fi @ FunctionInvocation(fdef, args) => Times(IntLiteral(c), fi)
        case Plus(e1, e2) => Plus(PushTimes(c, e1), PushTimes(c, e2))
        case Times(e1, e2) => {
          //here push the times into the coefficient (which should be the first expression)
          Times(PushTimes(c, e1), e2)
        }
        case _ => throw NotImplementedException("PushTimes -- Operators not yet handled: " + ine)
      }
    }

    //collect all the constants and simplify them
    //we assume that PushTimes and PushMinus have been invoked on the expression
    def simplifyConsts(ine: Expr): (Option[Expr], Int) = {
      require(ine.getType == Int32Type)

      ine match {
        case IntLiteral(v) => (None, v)
        case t: Terminal => (Some(t), 0)
        case fi: FunctionInvocation => (Some(fi), 0)
        case Plus(e1, e2) => {
          val (r1, c1) = simplifyConsts(e1)
          val (r2, c2) = simplifyConsts(e2)

          val newe = (r1, r2) match {
            case (None, None) => None
            case (Some(t), None) => Some(t)
            case (None, Some(t)) => Some(t)
            case (Some(t1), Some(t2)) => Some(Plus(t1, t2))
          }
          (newe, c1 + c2)
        }
        case Times(e1, e2) => {
          //because of the pushTimes assumption, we can simplify this case
          (Some(ine), 0)
        }
        case _ => throw NotImplementedException("collectConstants -- Operators not yet handled: " + ine)
      }
    }

    def mkLinearRecur(inExpr: Expr): Expr = {
      inExpr match {
        case e @ BinaryOperator(e1, e2, op) if (e1.getType == Int32Type &&
          (e.isInstanceOf[Equals] || e.isInstanceOf[LessThan]
            || e.isInstanceOf[LessEquals] || e.isInstanceOf[GreaterThan]
            || e.isInstanceOf[GreaterEquals])) => {

          val (newe, newop) = e match {
            case t: Equals => (Minus(e1, e2), op)
            case t: LessEquals => (Minus(e1, e2), LessEquals)
            case t: LessThan => (Plus(Minus(e1, e2), one), LessEquals)
            case t: GreaterEquals => (Minus(e2, e1), LessEquals)
            case t: GreaterThan => (Plus(Minus(e2, e1), one), LessEquals)
          }
          val r = mkLinearRecur(newe)
          //simplify the resulting constants
          val (Some(r2), const) = simplifyConsts(r)
          val finale = if (const != 0) Plus(r2, IntLiteral(const)) else r2
          //println(r + " simplifies to "+finale)
          newop(finale, zero)
        }
        case Minus(e1, e2) => Plus(mkLinearRecur(e1), PushMinus(mkLinearRecur(e2)))
        case UMinus(e1) => PushMinus(mkLinearRecur(e1))
        case Times(e1, e2) => {
          val (r1, r2) = (mkLinearRecur(e1), mkLinearRecur(e2))
          (r1, r2) match {
            case (IntLiteral(v), _) => PushTimes(v, r2)
            case (_, IntLiteral(v)) => PushTimes(v, r1)
            case _ => throw IllegalStateException("Expression not linear: " + Times(r1, r2))
          }
        }
        case Plus(e1, e2) => Plus(mkLinearRecur(e1), mkLinearRecur(e2))
        case t: Terminal => t
        case fi: FunctionInvocation => fi
        /*case UnaryOperator(e,op) => op(mkLinearRecur(e))
        case BinaryOperator(e1,e2,op) => op(mkLinearRecur(e1),mkLinearRecur(e2))
        case NAryOperator(args,op) => op(args.map(mkLinearRecur(_)))*/
        case _ => throw IllegalStateException("Expression not linear: " + inExpr)
      }
    }
    val rese = mkLinearRecur(atom)
    //println("Unnormalized Linearized expression: "+unnormLinear)
    rese
  }
 
  /**
   * The following procedure converts the formula into negated normal form by pushing all not's inside.
   * It also handles Not equal to operators
   */
  def TransformNot(expr: Expr): Expr = {
    def nnf(inExpr: Expr): Expr = {
      inExpr match {
        //matches integer binary relation
        case Not(e @ BinaryOperator(e1, e2, op)) if (e1.getType == Int32Type) => {
          e match {
            case e: Equals => Or(nnf(LessEquals(e1, Minus(e2, one))), nnf(GreaterEquals(e1, Plus(e2, one))))
            case e: LessThan => GreaterEquals(nnf(e1), nnf(e2))
            case e: LessEquals => GreaterThan(nnf(e1), nnf(e2))
            case e: GreaterThan => LessEquals(nnf(e1), nnf(e2))
            case e: GreaterEquals => LessThan(nnf(e1), nnf(e2))
            case _ => throw IllegalStateException("Unknown integer predicate: " + e)
          }
        }
        //TODO: Puzzling: "Not" is not recognized as an unary operator, need to find out why
        case e @ Not(t: Terminal) => e
        case Not(And(args)) => Or(args.map(arg => nnf(Not(arg))))
        case Not(Or(args)) => And(args.map(arg => nnf(Not(arg))))
        case Not(Not(e1)) => nnf(e1)
        case Not(Implies(e1, e2)) => And(nnf(e1), nnf(Not(e2)))
        case Not(Iff(e1, e2)) => Or(nnf(Implies(e1, e2)), nnf(Implies(e2, e1)))

        case t: Terminal => t
        case u @ UnaryOperator(e1, op) => op(nnf(e1))
        case b @ BinaryOperator(e1, e2, op) => op(nnf(e1), nnf(e2))
        case n @ NAryOperator(args, op) => op(args.map(nnf(_)))

        case _ => throw IllegalStateException("Impossible event: expr did not match any case: " + inExpr)
      }
    }
    nnf(expr)
  }

  /**   
   * The following code is tricky. It implements multiple functionalities together
   * (a) it replaces every function call by a variable and creates a new equality
   * (b) it also replaces arguments that are not variables by fresh variables and creates 
   * a new equality mapping the fresh variable to the argument expression   
   */   
  var fiToVarMap = Map[FunctionInvocation, Variable]()
  
  def FlattenFunction(inExpr: Expr): (Expr,Set[Expr],Set[Expr]) = {    
    var newConjuncts = Set[Expr]()
    var newUIFs = Set[Expr]()

    def flattenFunc(e: Expr): Expr = {
      e match {        
        case fi @ FunctionInvocation(fd, args) => {
          if(fiToVarMap.contains(fi)){
            fiToVarMap(fi)
          }            
          else {
            //create a new variable to represent the function
            val freshResVar = Variable(FreshIdentifier("r", true).setType(fi.getType))
            fiToVarMap += (fi -> freshResVar)                                    
            
            //now also flatten the args. The following is slightly tricky            
            var newctrs = Seq[Expr]()
            val newargs = args.map((arg) =>              
              arg match {                
                case t : Terminal => t                                     
                case _ => {                  
                  val (nexpr,nuifs,ncjs) = FlattenFunction(arg)
                  
                  newConjuncts ++= ncjs
                  newUIFs ++= nuifs 
                  
                  nexpr match {
                    case t : Terminal => t
                    case _ => {
                    	val freshArgVar = Variable(FreshIdentifier("arg", true).setType(arg.getType))                    	                    	
                        newConjuncts += Equals(freshArgVar, nexpr) 
                        freshArgVar
                    }
                  }                                    
                }
              })
             //create a new equality in UIFs
             val newfi = FunctionInvocation(fd,newargs)                          
            newUIFs += Equals(freshResVar,newfi)
            freshResVar
          }                                
        }
        case _ => e
      }
    }
    var newExpr = simplePostTransform(flattenFunc)(inExpr)
    (newExpr,newUIFs,newConjuncts)
  }

  //some utility methods
  def getFIs(ctr: LinearConstraint): Set[FunctionInvocation] = {
    val fis = ctr.coeffMap.keys.collect((e) => e match {
      case fi: FunctionInvocation => fi
    })
    fis.toSet
  }

  /*def CtrsToExpr(ctrs : Set[Linear]) : Expr ={
    And(ctrs.map(_.template).toSeq)
  } */  
  

  /**
   * This function computes invariants belonging to the template.
   * The result is a mapping from function definitions to the corresponding invariants.
   * Note that the invariants are context specific and may not be context independent invariants for the functions (except for inFun)
   */
  def solveForTemplates(inFun: FunDef, tempSynth: (Seq[Expr],FunDef) => Set[LinearTemplate], 
      inTemplates: Set[LinearTemplate], uiSolver : UninterpretedZ3Solver): Option[Map[FunDef, Expr]] = {
    
    //generate templates for the calls in UIFs
    var templateMap = Map[Expr,Set[LinearTemplate]]()
    def uifTemplatesGen(call: Expr) = {      
      call match {
        case Equals(v@Variable(_),fi@FunctionInvocation(fd,args)) => {
          templateMap.getOrElse(call, {
        	  val temp = tempSynth(args :+ v,fd)
        	  templateMap += (call -> temp)
        	  temp
          })          
        }
        case _ => Set[LinearTemplate]()
      }      
    }

    //this could take 2^(n^2) time
    def uifsConstraintsGen(calls: Set[Expr], ctrs: Seq[LinearConstraint], pathexpr: Expr): Seq[Seq[LinearConstraint]] = {
      //now create a  uif tree for this path by reducing the UIFs to the base theory.             
      val uifCtrs = constraintsForUIFs(calls, pathexpr, uiSolver)
      val uifroot = if (!uifCtrs.isEmpty) {
        val uifCtr = And(uifCtrs)
        println("UIF constraints: " + uifCtr)
        //push not inside
        val nnfExpr = TransformNot(uifCtr)
        //create the root of the UIF tree
        //TODO: create a UIF tree once and for all and prune the paths while traversing
        val newnode = CtrNode(FreshIdentifier("uifroot", true))
        //add the nnfExpr as a DNF formulae
        addConstraintRecur(nnfExpr, newnode)
        newnode
      } else CtrLeaf()

      var outputCtrs = Seq[Seq[LinearConstraint]]()
      def traverseUIFtree(tree: CtrTree, currentCtrs: Seq[LinearConstraint]): Unit = {
        tree match {
          case n @ CtrNode(_) => {
            val newCtrs = currentCtrs ++ n.constraints
            //recurse into children
            for (child <- n.Children)
              traverseUIFtree(child, newCtrs)
          }
          case CtrLeaf() => {
            outputCtrs +:= currentCtrs
          }
        }
      }

      traverseUIFtree(uifroot, ctrs)
      outputCtrs
    }

    def constraintsToExpr(ctrs: Seq[LinearConstraint], calls: Set[Expr]): Expr = {
      //compute the path expression corresponding to the paths
      //note: add the UIFs in to the path condition
      val pathExpr = And(ctrs.foldLeft(Seq[Expr]())((acc, ctr) => (acc :+ ctr.expr)))
      And(pathExpr, And(calls.toSeq))
    }

    //first traverse the body and collect all the antecedents               
    var antSet = List[(Set[LinearConstraint],Set[LinearTemplate])]()

    //this tree could have 2^n paths 
    def traverseBodyTree(tree: CtrTree, currentCtrs: Seq[LinearConstraint], currentUIFs: Set[Expr]): Unit = {
      tree match {
        case n @ CtrNode(blkid) => {
          val newCtrs = currentCtrs ++ n.constraints
          val newUIFs = currentUIFs ++ n.uifs
          //recurse into children
          for (child <- n.Children)
            traverseBodyTree(child, newCtrs, newUIFs)
        }
        case CtrLeaf() => {

          val pathexpr = constraintsToExpr(currentCtrs, currentUIFs)
          val (res, model, unsatCore) = uiSolver.solveSATWithFunctionCalls(pathexpr)
          if (!res.isDefined || res.get == true) {

            println("Path expr: " + pathexpr)

            //TODO: assuming templates only for the input function
            val uifTemps = currentUIFs.filter((call) => call match {
              
              case Equals(_,FunctionInvocation(fd,args)) => fd == inFun
              case _ => false
              
            }).flatten(uifTemplatesGen(_))
            
            antSet ++= uifsConstraintsGen(currentUIFs, currentCtrs, pathexpr).map((ctrs) => (ctrs.toSet, uifTemps))
          } else {
            //println("Found unsat path: " + pathExpr)
          }
        }
      }
    }
        
    def traversePostTree(tree: CtrTree,conseqs: Seq[LinearConstraint], currUIFs: Set[Expr]): Option[Expr] = {
      tree match {
        case n @ CtrNode(blkid) => {          
          val newcons = conseqs ++ n.constraints
          val newuifs = currUIFs ++ n.uifs 
          //recurse into children as along as we haven't found an invariant
          var aInvariant : Option[Expr] = None
          n.Children.takeWhile(_ => aInvariant == None).foreach((child) => { aInvariant = traversePostTree(child, newcons, newuifs) })
          aInvariant
        }
        case CtrLeaf() => {
          //here we need to check if the every antecedent in antSet implies the conseqs of this path 
          val nonLinearCtr = antSet.foldLeft(BooleanLiteral(true): Expr)((acc1, ants) => {

            if (acc1 == BooleanLiteral(false))
              acc1
            else {
              //TODO assuming that the post-condition wouldn't call the input function
              
              val (antCtrs,antTemps) = (ants._1.toSeq, ants._2.toSeq)                           
              val pathexpr = constraintsToExpr(antCtrs,currUIFs)                            
              val antlists = uifsConstraintsGen(currUIFs, antCtrs, pathexpr)

              antlists.foldLeft(acc1)((acc2, newant) => {

                if (acc2 == BooleanLiteral(false))
                  acc2
                else {
                  val newCtr = implicationSolver.constraintsForImplication(newant, antTemps, conseqs, inTemplates.toSeq, uiSolver)
                  newCtr match {
                    case BooleanLiteral(true) => acc2 //nothing to add as no new constraints are generated              
                    case fls @ BooleanLiteral(false) => fls //entire set of constrains are unsat
                    case _ => if (acc2 == BooleanLiteral(true)) newCtr
                    else And(acc2, newCtr)
                  }
                }
              })              
            }
          })   
          
          nonLinearCtr match { 
            case BooleanLiteral(true) => throw IllegalStateException("The original postcondition is inductive, nothing to infer")
            case BooleanLiteral(false) => None //skip to the next leaf
            case _ => {
              //look for a solution of non-linear constraints. The constraint variables are all reals
              //println("Non linear constraints for this branch: " +nonLinearCtr)          
              val (res, model, unsatCore) = uiSolver.solveSATWithFunctionCalls(nonLinearCtr)              
              if (res.isDefined && res.get == true) {
                //printing the model here for debugging
                //println("Model: "+model)
                //construct an invariant (and print the model)
                val invs = inTemplates.map((inTemp) => {
                  val coeff = inTemp.coeffTemplate.map((entry) => {
                    val (k, v) = entry
                    v match {
                      case Variable(id) => (k, model(id))
                      case _ => (k, v)
                    }
                  })
                  val const = inTemp.constTemplate match {
                    case Some(Variable(id)) => model(id)
                    case Some(t) => t
                    case None => zero
                  }
                  //the coefficients could be fractions ,so collect all the denominators
                  val getDenom = (t: Expr) => t match {
                    case RealLiteral(num, denum) => denum
                    case _ => 1
                  }

                  val denoms = coeff.foldLeft(Set(getDenom(const)))((acc, entry) => acc + getDenom(entry._2))
                  //compute the LCM of the denominators (approx. LCM)
                  val lcm = denoms.foldLeft(1)((acc, d) => if (acc % d == 0) acc else acc * d)

                  //scale the numerator by lcm
                  val scaleNum = (t: Expr) => t match {
                    case RealLiteral(num, denum) => IntLiteral(num * (lcm/denum))
                    case IntLiteral(n) => IntLiteral(n * lcm)
                    case _ => throw IllegalStateException("Coefficient not assigned to any value")
                  }

                  val expr = coeff.foldLeft(scaleNum(const): Expr)((acc, entry) => {
                    val (k, v) = entry
                    Plus(acc, Times(k, scaleNum(v)))
                  })

                  LessEquals(expr, zero)
                })
                val invariant = And(invs.toSeq)
                Some(invariant)
              } else {
                println("Constraint Unsat: "+unsatCore)
                None
              }              
            }            
          }          
        }
      }
    }

    //traverse the bodyTree and postTree 
    traverseBodyTree(bodyRoot, Seq[LinearConstraint](), Set[Expr]())
    val inv = traversePostTree(postRoot,Seq[LinearConstraint](),Set[Expr]())

    if(inv.isDefined)
      Some(Map(inFun -> inv.get))
    else None 
  }

  
  //convert the theory formula into linear arithmetic formula
  //TODO: Handle ADTs also  
  def constraintsForUIFs(calls: Set[Expr], precond: Expr, uisolver: UninterpretedZ3Solver) : Seq[Expr] = {
        
    //Part(I): Finding the set of all pairs of funcs that are implied by the precond
    var impliedGraph = new UndirectedGraph[Expr]()
    var nimpliedSet = Set[(Expr,Expr)]()
    
    //compute the cartesian product of the calls and select the pairs having the same function symbol and also implied by the precond
    val product = calls.foldLeft(Set[(Expr,Expr)]())((acc, call) => {
      val Equals(v,FunctionInvocation(fd,args)) = call
      val pairs = calls.collect((call2) => call2 match {
        case Equals(_,FunctionInvocation(fd2,_)) if (call != call2 && fd == fd2) => (call,call2) 
      })
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
              nimpliedSet ++= Set((call1,call2),(call2,call1))                       
              //TODO: consider the following optimization :
              //take the model found in this case. If the instantiation of the template does not satisfy the model
              //then may be it could imply the equality. So, we could try this case later. 
            }
          }                  
        }                     
      }
    })    
    
    //Part (II) return the constraints. For each implied call, the constraints are just that their return values are equal.
    //For other calls the constraints are full implication    
    val edges = impliedGraph.Edges.toSet         
    val newctrs = product.foldLeft(Seq[Expr]())((acc,pair) => {
      val (call1,call2)= pair
      val Equals(v1,fi1) = call1
      val Equals(v2,fi2) = call2
      if(edges.contains(pair)) {
        acc :+ Equals(v1,v2)
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
   * TODO: how can we handle functions with templates variables and functions with template names
   */
  def axiomatizeEquality(call1: Expr, call2: Expr): (Expr, Expr) = {
    (call1, call2) match {
      case (Equals(v1 @ Variable(_), fi1 @ FunctionInvocation(_, _)), Equals(v2 @ Variable(_), fi2 @ FunctionInvocation(_, _))) => {
        val ants = (fi1.args.zip(fi2.args)).foldLeft(Seq[Expr]())((acc, pair) => {
          val (arg1, arg2) = pair
          acc :+ Equals(arg1, arg2)
        })
        val conseq = Equals(v1, v2)
        (And(ants), conseq)
      }
    }
  } 
  
  /**
   * This function returns all the calls in the in the linear template
   * Assumes that all function invocations have been flattened.
   */
  /*def getAllCalls(lt : LinearTemplate) : Iterable[Expr] = {
    lt.template match {
      case Equals(Variable(_),FunctionInvocation(_,_)) => {
          Seq(lt.template)
        } 
      case _  if(lt.coeffTemplate.keys.find(_.isInstanceOf[FunctionInvocation]).isDefined) => {
        throw IllegalStateException("FunctionInvocations not flattened in "+lt.template)  
      }
      case _ => Seq()
    }    
  }
*/
}