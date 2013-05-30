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

//Class representing linear templates which is a constraint of the form a1*v1 + a2*v2 + .. + an*vn + a0 <= 0 or = 0 where a_i's can be free vars
case class LinearTemplate(val template: Expr, val coeffTemplate: Map[Expr, Expr with Terminal], 
	val constTemplate: Option[Expr with Terminal]) {
		
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
object GlobalNodeCounter {
	var id = 0	
	def getUID : Int = {
	  id += 1
	  id
	} 
}

//TODO: create a new id for each CtrNode
case class CtrNode(id : Int = GlobalNodeCounter.getUID) extends CtrTree {

	//constraints
  var constraints = Set[LinearConstraint]()
  //templates that aren't constraints
  var templates = Set[LinearTemplate]()
  //UI function calls
  var uifs = Set[Call]()
  //children in the DNF tree
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

  def getEndNode : CtrNode = {    
  	if(children.first == CtrLeaf()) this
  	else {
  	 val n@CtrNode(_) = children.first
  	 n.getEndNode
  	}
  }

  override def toString(): String = {
    var str = " Constriants: " + constraints + " children: \n"
    children.foldLeft(str)((g: String, node: CtrTree) => { g + node.toString })
  }
}

class ConstraintTracker(fundef : FunDef) {

  private val implicationSolver = new LinearImplicationSolver()
  //this is a mutable map (used for efficiency)
  //private var treeNodeMap = collection.mutable.Map[Identifier, CtrNode]()
  
  //verification conditions for each procedure that may have templates.
  //Each verification condition is an implication where the antecedent and the consequent are represented as DNF trees.
  private var templatedVCs = Map[FunDef,(CtrNode,CtrNode)]()
  
  //some identifiers representing body start and post start
  //val bstart = FreshIdentifier("bstart")
  //val pstart = FreshIdentifier("pstart")
  
  /*//This would be set while constraints are added
  //body and post are DNF formulas and hence are represented using trees
  private var bodyRoot = CtrNode()
  private var postRoot = CtrNode()    
  */
  //some constants
  private val zero = IntLiteral(0)
  private val one = IntLiteral(1)
  private val mone =IntLiteral(-1)   
  private val fls = BooleanLiteral(false)
  private val tru = BooleanLiteral(true)

  //adds a constraint in conjunction with  the constraint represented by parentNode
  def addConstraintRecur(inexpr: Expr, parentNode : CtrNode) : Unit = {

    //returns a node that represents the root of the constraint
    //this is passed an end node: the node that represents the last  children of the sub-tree
    def addCtr(ie: Expr, endnode: CtrNode): CtrNode = {
      ie match {
        case Or(subexprs) => {
          val children = subexprs.foldLeft(Set[CtrNode]())((acc, sube) => {                   
            acc + addCtr(sube, endnode)
          })
          val rootnode = CtrNode()          
          children.foreach((child) => { rootnode.addChildren(child); })
          rootnode
        }
        case And(subexprs) => {
          val rootnode = subexprs.foldRight(None: Option[CtrNode])((sube, acc) => {
            val currentNode = if (acc == None) addCtr(sube, endnode)
            else addCtr(sube, acc.get)
            Some(currentNode)
          })
          rootnode.get
        }        	    
        case _ => {
          val node = CtrNode()          
          ie match {
            case Equals(v@Variable(_),fi@FunctionInvocation(_,_)) => {
            	node.uifs += Call(v,fi)
            }
            case _ => {
              val ctr = exprToConstraint(ie)          
              node.constraints += ctr
            } 
          }          
          node.addChildren(endnode)
          node
        }
      }
    }
    val exprRoot = addCtr(inexpr, CtrNode())
    val parentEnd = parentNode.getEndNode
    parentEnd.addChildren(exprRoot)    
  }
  
  //some utility methods
  /*def isBlockingId(id: Identifier): Boolean = {
    if (id.name.startsWith("b")) true else false
  }

  def isStartId(id: Identifier): Boolean = {
    if (id.name.contains("start")) true else false
  }*/  

  def addConstraint(e: Expr, bodyRoot: CtrNode, postRoot: CtrNode, isBody: Boolean) = {

    //println("Expression after Not transformation: "+nnfExpr)
    //val (id, innerExpr) = parseGuardedExpr(nnfExpr)
    //get the node corresponding to the id
    /*val ctrnode = nodeMap.getOrElse(id, {
      val node = if(isStartId(id)){
        if(isBody) bodyRoot
        else postRoot
      }
      else CtrNode(id)
      nodeMap += (id -> node)
      node
    })*/
    //flatten function returns a new expresion without function symbols and a set of newly created equalities
    //val flatExpr = InvariantUtil.FlattenFunction(nnfExpr)         
    val root = if(isBody) bodyRoot else postRoot    
    addConstraintRecur(e, root)           
  }

  //checks if a constraint tree exists for a function 
  def hasCtrTree(fdef: FunDef) = {
  	templatedVCs.contains(fdef)
  }

	//returns the constraint tree corresponding to a function
  def getCtrTree(fdef: FunDef) : (CtrNode,CtrNode) ={
    templatedVCs.getOrElse(fdef, {
      //initialize body and post roots
      val newentry = (CtrNode(),CtrNode())
      templatedVCs += (fdef -> newentry)
      newentry
    })    
  }

  def addBodyConstraints(fdef: FunDef, body: Expr) = {
    val (bodyRoot,postRoot) = getCtrTree(fdef)    
    addConstraint(body, bodyRoot, postRoot, true)
  }

  /**
   * This is a little tricky the post tree contains negation of the post condition.
   * This is used for optimization.  
   */
  def addPostConstraints(fdef: FunDef, npost: Expr) = {
    val (bodyRoot,postRoot) = getCtrTree(fdef)
    addConstraint(npost, bodyRoot, postRoot, false)
    //println("PostCtrTree\n"+postRoot.toString)    
  }

  /**
   * This is a little tricky. The postRoot is used to store all the templates
   * TODO: assumption the templates are assume to not have disjunctions
   */
  def addTemplatedPostConstraints(fdef: FunDef, temp: LinearTemplate) = {
    val (_, postRoot) = getCtrTree(fdef)
    postRoot.templates += temp
    /*val child = CtrNode()
    child.templates += temp
    postRoot.addChildren(child)*/
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
   */
  def solveForTemplates(tempSynth: TemplateFactory,
    uiSolver: UninterpretedZ3Solver): Option[Map[FunDef, Expr]] = {

    //traverse each of the functions and collect the constraints
    val nonLinearCtrs  = templatedVCs.foldLeft(Seq[Expr]())((acc, elem) => {
      val ctr = generateCtrsForTree(elem._2._1, elem._2._2, tempSynth, uiSolver)      
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
      val invs = tempSynth.getFunctions.map((fd) => {
        val coeff = tempSynth.getCoeff(fd).map((v) => {
          //println(v.id +" mapsto " + model(v.id))
          model(v.id)
        })
        /*val const = inTemp.constTemplate match {
                    case Some(Variable(id)) => model(id)
                    case Some(t) => t
                    case None => zero
                  }*/
        //the coefficients could be fractions ,so collect all the denominators
        val getDenom = (t: Expr) => t match {
          case RealLiteral(num, denum) => denum
          case _ => 1
        }

        val denoms = coeff.foldLeft(Set[Int]())((acc, entry) => { acc + getDenom(entry) } )
        //compute the LCM of the denominators (approx. LCM)
        val lcm = denoms.foldLeft(1)((acc, d) => if (acc % d == 0) acc else acc * d)

        //scale the numerator by lcm
        val scaleNum = (t: Expr) => t match {
          case RealLiteral(num, denum) => IntLiteral(num * (lcm / denum))
          case IntLiteral(n) => IntLiteral(n * lcm)
          case _ => throw IllegalStateException("Coefficient not assigned to any value")
        }
        val intCoeffs = coeff.map(scaleNum(_))
        val constPart :: coeffPart = intCoeffs
        val argsCoeff = (fd.args.map(_.id.toVariable) :+ ResultVariable()).zip(coeffPart)

        val expr = argsCoeff.foldLeft(constPart: Expr)((acc, entry) => {
          val (k, v) = entry
          Plus(acc, Times(k, v))
        })
        val ctr = LessEquals(expr, zero)
        
        /*//here negate the template as the invariant is the negation of the template
        val inv = InvariantUtil.TransformNot(Not(ctr))*/
        (fd -> ctr)
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
  def generateCtrsForTree(bodyRoot: CtrNode, postRoot : CtrNode, tempSynth: TemplateFactory, 
      uiSolver : UninterpretedZ3Solver) : Expr = {
    
    //generate templates for the calls in UIFs
    var templateMap = Map[Call,Set[LinearTemplate]]()
    def uifTemplatesGen(call: Call) = {      
      templateMap.getOrElse(call, {
    	  val temp = tempSynth.constructTemplate(call.fi.args :+ call.retexpr, call.fi.funDef)
    	  templateMap += (call -> temp)
    	  temp
      })                     
    }
    
    def constraintsToExpr(ctrs: Seq[LinearConstraint], calls: Set[Call]): Expr = {
      //compute the path expression corresponding to the paths
      //note: add the UIFs in to the path condition
      val pathExpr = And(ctrs.foldLeft(Seq[Expr]())((acc, ctr) => (acc :+ ctr.expr)))
      val uifExpr = And(calls.map((call) => Equals(call.retexpr,call.fi)).toSeq)
      And(pathExpr, uifExpr)
    }

    //this could take 2^(n^2) time
    def uifsConstraintsGen(calls: Set[Call], ctrs: Seq[LinearConstraint], pathexpr: Expr)
    : Seq[Seq[LinearConstraint]] = {
      //now create a  uif tree for this path by reducing the UIFs to the base theory.             
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
      //println("outputCtrs: "+outputCtrs)
      outputCtrs
    }
    
    //first traverse the body and collect all the antecedents               
    //var antSet = List[(Set[LinearConstraint],Set[LinearTemplate])]()
    var antSet = List[(Set[LinearConstraint],Set[Call])]()

    //this tree could have 2^n paths 
    def traverseBodyTree(tree: CtrTree, currentCtrs: Seq[LinearConstraint], currentUIFs: Set[Call]): Unit = {
      tree match {
        case n @ CtrNode(_) => {
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
            antSet :+= (currentCtrs.toSet,currentUIFs)
            
            //val uifTemps = currentUIFs.filter((call) => hasCtrTree(call.fi.funDef)).flatten(uifTemplatesGen(_))            
            //antSet ++= uifsConstraintsGen(currentUIFs, currentCtrs, pathexpr).map((ctrs) => (ctrs.toSet, uifTemps))
            
          } else {
            //println("Found unsat path: " + pathExpr)
          }
        }
      }
    }
        
    //TODO: not clear why there are uifs in the post-condition
    def traversePostTree(tree: CtrTree,conseqs: Seq[LinearConstraint], currUIFs: Set[Call], 
    					currTemps: Seq[LinearTemplate]): Expr = {
    						
      tree match {
        case n @ CtrNode(_) => {          
          val newcons = conseqs ++ n.constraints
          val newuifs = currUIFs ++ n.uifs 
          val newtemps = currTemps ++ n.templates
          
          //recurse into children and collect all the constraints
          var exprs = Seq[Expr]()
          n.Children.foreach((child) => {
            val ctr = traversePostTree(child, newcons, newuifs, newtemps)            
            exprs :+= ctr
          })
          //any one of the branches must hold
          if(exprs.isEmpty) BooleanLiteral(true)         
          else if(exprs.size == 1) exprs.first
          else And(exprs)
        }
        case CtrLeaf() => {         
          //here we need to check if the every antecedent in antSet and the conseqs of the path is unsat i.e, false           
          val nonLinearCtr = antSet.foldLeft(BooleanLiteral(true): Expr)((acc1, ants) => {

            if (acc1 == BooleanLiteral(false))
              acc1
            else {
              //TODO assuming that the post-condition wouldn't call the input function
              val (antCtrs,antCalls) = (ants._1.toSeq, ants._2)     
              val calls = antCalls ++ currUIFs
              
              val pathexpr = constraintsToExpr(antCtrs, calls)                            
              val antlists = uifsConstraintsGen(calls, antCtrs, pathexpr)
              val antTemps = calls.filter((call) => hasCtrTree(call.fi.funDef)).flatten(uifTemplatesGen(_))            
                            
              /*val (antCtrs,antTemps) = (ants._1.toSeq, ants._2.toSeq)                           
              val pathexpr = constraintsToExpr(antCtrs,currUIFs)                            
              val antlists = uifsConstraintsGen(currUIFs, antCtrs, pathexpr)*/
              //println("Ant Lists: "+antlists)
              antlists.foldLeft(acc1)((acc2, newant) => {

                if (acc2 == BooleanLiteral(false))
                  acc2
                else {
                  //here we are solving A^~(B)
                  val newCtr1 = implicationSolver.constraintsForUnsat(newant, antTemps.toSeq, conseqs, Seq(), uiSolver)
                  //here we are solving for A => T
                  val newCtr2 = implicationSolver.constraintsForImplication(newant, antTemps.toSeq, Seq(), currTemps, uiSolver)
                  
                  //doing some simplifications 
                  val newCtr = if (newCtr1 == tru)
                    newCtr2
                  else if (newCtr2 == tru)
                    newCtr1
                  else if (newCtr1 == fls || newCtr2 == fls)
                    fls
                  else And(newCtr1, newCtr2)
                  
                  newCtr match {                                 
                    case BooleanLiteral(false) => fls //entire set of constraints are sat 
                    case _ => if (acc2 == BooleanLiteral(true)) newCtr
                    else And(acc2, newCtr)
                  }
                }
              })              
            }
          })   
          
          nonLinearCtr match {            
            case BooleanLiteral(true) => throw IllegalStateException("Found no constraints")
            case _ => {
              //for debugging
              /*val (res, model, unsatCore) = uiSolver.solveSATWithFunctionCalls(nonLinearCtr)
              if(res.isDefined && res.get == true){
                println("Found solution for constraints")
              }*/              
              nonLinearCtr                        
            }
          }          
        }
      }
    }
    
    traverseBodyTree(bodyRoot, Seq[LinearConstraint](), Set[Call]())
    traversePostTree(postRoot,Seq[LinearConstraint](),Set[Call](),Seq[LinearTemplate]())
  }

  
  //convert the theory formula into linear arithmetic formula
  //TODO: Handle ADTs also  
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
      if(edges.contains(pair)) {
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
   * TODO: how can we handle functions with templates variables and functions with template names
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