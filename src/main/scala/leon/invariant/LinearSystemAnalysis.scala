package leon
package invariant

import z3.scala._
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
  private var treeNodeMap = collection.mutable.Map[Identifier, CtrNode]()
  //root of the tree. This would be set while constraints are added
  private var bodyRoot: CtrTree = CtrLeaf()
  private var postRoot: CtrTree = CtrLeaf()
  private val zero = IntLiteral(0)
  private val one = IntLiteral(1)
  private val mone =IntLiteral(-1)

  //some utility methods
  def isBlockingId(id: Identifier): Boolean = {
    if (id.name.startsWith("b")) true else false
  }

  def isStartId(id: Identifier): Boolean = {
    if (id.name.contains("start")) true else false
  }

  def addBodyConstraints(body: Seq[Expr]) = {
    val setBodyRoot = (node: CtrTree) => {
      if (bodyRoot == CtrLeaf()) bodyRoot = node
    }
    body.map(addConstraint(_, setBodyRoot))
  }

  def addPostConstraints(post: Seq[Expr]) = {
    val setPostRoot = (node: CtrTree) => {
      if (postRoot == CtrLeaf()) postRoot = node
    }
    post.map(addConstraint(_, setPostRoot))
    //clear the treeNodeMap here so that we reuse for the body 
    //TODO: Maintenance Issue: fix this and make treeNodeMap a parameter
    treeNodeMap.clear()
  }  

  def addConstraint(e: Expr, setRoot: (CtrTree => Unit)) = {
    val (id, innerExpr) = parseGuardedExpr(e)

    //get the node corresponding to the id
    val ctrnode = treeNodeMap.getOrElse(id, {
      val node = CtrNode(id)
      treeNodeMap += (id -> node)

      //set the root of the tree (this code is ugly and does string matching)
      //TODO: Maintenance Issue:  fix this
      if (isStartId(id)) setRoot(node)
      node
    })

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
            (Set(createOrLookupId(ctrnode, childId)), Set())
          } else
            throw IllegalStateException("Encountered a variable that is not a blocking id: " + childId)
        }
        case Iff(lhs, rhs) => {
          //lhs corresponds to a blocking id in this case
          lhs match {
            case Variable(childId) if (isBlockingId(childId)) => {
              val childNode = createOrLookupId(ctrnode, childId)
              val ctr = exprToConstraint(rhs)
              childNode.constraints += ctr
              (Set(childNode), Set())
            }
            case _ => throw IllegalStateException("Iff block --- encountered something that is not a blocking id: " + lhs)
          }

        }
        case _ => {
          val node = if (newChild) createOrLookupId(ctrnode, FreshIdentifier("dummy", true))
          else ctrnode
          val ctr = exprToConstraint(ie)
          node.constraints += ctr
          if (newChild) (Set(), Set(node)) else (Set(), Set())
        }
      }
    }
    //important: calling makelinear may result in disjunctions and also potentially conjunctions
    val flatExpr = FlattenFunction(innerExpr)
    val nnfExpr = TransformNot(flatExpr)
    val (realChildren, dummyChildren) = addCtrOrBlkLiteral(nnfExpr, false)

    //now merge dummy children with the ctrnode itself.
    //the following code is slightly nasty and with side effects
    val parentNode = if (!dummyChildren.isEmpty) {
      val newnode = CtrNode(ctrnode.blockingId)
      ctrnode.copyChildren(newnode)
      ctrnode.removeAllChildren()
      dummyChildren.foreach((child) => { child.addChildren(newnode); ctrnode.addChildren(child) })
      treeNodeMap.update(ctrnode.blockingId, newnode)
      newnode
    } else ctrnode

    realChildren.foreach(parentNode.addChildren(_))
  }

  def createOrLookupId(parentNode: CtrNode, childId: Identifier): CtrNode = {
    var childNode = treeNodeMap.getOrElse(childId, {
      val node = CtrNode(childId)
      treeNodeMap += (childId -> node)
      node
    })
    childNode
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
   * This is a little tricky. Here we need keep identify function calls that are equivalent
   * and call them by the same name. Ideally this requires congruence closure algorithm.
   * TODO: Feature: handle uninterpreted functions
   */
  var processedFIs = Map[FunctionInvocation, FunctionInvocation]()
  def FlattenFunction(inExpr: Expr): Expr = {
    var conjuncts = Set[Expr]()

    def flattenFunc(e: Expr): Expr = {
      e match {
        case fi @ FunctionInvocation(fd, args) => {
          //check if the function invocation already exists
          val res = processedFIs.getOrElse(fi, {
            //flatten the  arguments            
            val newargs = args.foldLeft(List[Expr with Terminal]())((acc, arg) =>
              arg match {
                case t: Terminal => (acc :+ t)
                case arge @ _ => {
                  val freshvar = Variable(FreshIdentifier("arg", true).setType(arge.getType))
                  conjuncts += Equals(freshvar, arge)
                  (acc :+ freshvar)
                }
              })
            val newfi = FunctionInvocation(fd, newargs)
            processedFIs += (fi -> newfi)
            newfi
          })
          res
        }
        case _ => e
      }
    }
    var newExpr = simplePostTransform(flattenFunc)(inExpr)
    And((conjuncts + newExpr).toSeq)
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
  def solveForTemplates(inFun: FunDef, tempSynth: FunctionInvocation => Set[LinearTemplate], 
      inTemplates: Set[LinearTemplate], uiSolver : UninterpretedZ3Solver): Option[Map[FunDef, Expr]] = {
    //val templateMap = Map[Identifier,Set[LinearConstraint]]()     

    //first traverse the body and collect all the antecedents               
    var antSet = List[(Set[LinearConstraint], Set[LinearTemplate])]()

    def traverseBodyTree(tree: CtrTree, currentCtrs: Seq[LinearConstraint], currentTemps: Seq[LinearTemplate]): Unit = {
      tree match {
        case n @ CtrNode(blkid) => {
          val ctrs = n.constraints
          val newCtrs = currentCtrs ++ ctrs
          //find function invocations in ctrs
          val fis = ctrs.foldLeft(Set[FunctionInvocation]())((set, ctr) => set ++ getFIs(ctr))
          //generate a template for each function invocation and add it to the antecedents or consequent.
          //For now we consider on the function invocations of the input procedure only
          //TODO: Feature: Extend this to function invocations of other procedures
          val newTemps = fis.filter(_.funDef.equals(inFun)).foldLeft(currentTemps)((acc, fi) => {
            val invt = tempSynth(fi)
            acc ++ invt
          })
          //recurse into children
          for (child <- n.Children)
            traverseBodyTree(child, newCtrs, newTemps)
        }
        case CtrLeaf() => {
          //add the currnetCtrs only if it is not unsat
          val pathExpr = And(currentCtrs.foldLeft(Seq[Expr]())((acc, ctr) => (acc :+ ctr.expr)))
          val (res, model) = uiSolver.solveSATWithFunctionCalls(pathExpr)

          if (!res.isDefined || res.get == true) {
            //antCtrSet +:= currentCtrs.toSet
            //antTempSet +:= currentTemps.toSet
            antSet +:= (currentCtrs.toSet, currentTemps.toSet)
          } else {
            println("Found unsat path: " + pathExpr)
          }
        }
      }
    }

    def traversePostTree(tree: CtrTree, postAnts: Seq[LinearTemplate], conseqs: Seq[LinearConstraint]): Option[Expr] = {
      tree match {
        case n @ CtrNode(blkid) => {
          val ctrs = n.constraints
          var newcons = conseqs ++ ctrs
          var newants = postAnts
          //find function invocations in ctrs
          val fis = ctrs.foldLeft(Set[FunctionInvocation]())((set, ctr) => set ++ getFIs(ctr))
          //generate a template for each function invocation and add it to the antecedents.          
          for (fi <- fis.filter(_.funDef.equals(inFun))) {
            val invt = tempSynth(fi)
            newants ++= invt
          }
          //recurse into children
          var aInvariant : Option[Expr] = None
          n.Children.takeWhile(_ => aInvariant == None).foreach((child) => { aInvariant = traversePostTree(child, newants, newcons) })
          aInvariant
        }
        case CtrLeaf() => {
          //here we need to check if the every antecedent in antSet implies the conseqs of this path 
          val nonLinearCtrs = antSet.foldLeft(null: Expr)((acc, ants) => {

            //this is an optimization (check if ants._1 => conseqs._1) is unsat if yes 
            //pass this information on to the NonLinear ctr generator
            val pathVC = Implies(And(ants._1.map(_.expr).toSeq), And(conseqs.map(_.expr).toSeq))
            val (satRes, _) = uiSolver.solveSATWithFunctionCalls(pathVC)
            val disableAnts = if (satRes.isDefined && satRes.get == false) true else false

            val allAnts = (ants._1 ++ ants._2 ++ postAnts)
            val allConseqs = conseqs ++ inTemplates
            //for debugging
            println("#" * 20)
            println(allAnts + " => " + allConseqs)
            println("#" * 20)

            //here we know that the antecedents are satisfiable
            val newCtrs = implicationSolver.applyFarkasLemma(allAnts.toSeq, allConseqs, disableAnts)            
            if (acc == null) newCtrs
            else And(acc, newCtrs)
          })                    
          
          //look for a solution of non-linear constraints by interpreting all integers as Reals
          //println("Non linear constraints for this branch: " +nonLinearCtrs)          
          val (res, model) = uiSolver.solveSATWithFunctionCalls(nonLinearCtrs)
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
              val expr = coeff.foldLeft(const)((acc, entry) => Plus(acc, Times(entry._1, entry._2)))
              LessEquals(expr,zero)
            })
            val invariant = And(invs.toSeq)
            Some(invariant)
          } else {
            None
          }
        }
      }
    }

    //traverse the bodyTree and postTree 
    traverseBodyTree(bodyRoot, Seq[LinearConstraint](), Seq[LinearTemplate]())
    val inv = traversePostTree(postRoot, Seq[LinearTemplate](), Seq[LinearConstraint]())

    if(inv.isDefined)
      Some(Map(inFun -> inv.get))
    else None 
  }

}