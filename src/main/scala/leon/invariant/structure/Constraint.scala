package leon
package invariant.structure

import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import invariant.util._
import PredicateUtil._
import TypeUtil._
import purescala.Extractors._

trait Constraint {
  def toExpr: Expr
}
/**
 * Class representing linear templates which is a constraint of the form
 * a1*v1 + a2*v2 + .. + an*vn + a0 <= 0 or = 0 or < 0 where ai's are unknown coefficients
 * which could be any arbitrary expression with template variables as free variables
 * and vi's are variables.
 * Note: we need atleast one coefficient or one constant to be defined.
 * Otherwise a NPE will be thrown (in the computation of 'template')
 */
class LinearTemplate(oper: Seq[Expr] => Expr,
  coeffTemp: Map[Expr, Expr],
  constTemp: Option[Expr]) extends Constraint {

  val zero = InfiniteIntegerLiteral(0)

  val op = {
    oper
  }
  val coeffTemplate = {
    //assert if the coefficients are templated expressions
    assert(coeffTemp.values.forall(e => isTemplateExpr(e)))
    coeffTemp
  }

  val constTemplate = {
    assert(constTemp match {
      case None => true
      case Some(e) => isTemplateExpr(e)
    })
    constTemp
  }

  val template = {
    //construct the expression corresponding to the template here
    var lhs = coeffTemp.foldLeft(null: Expr)((acc, entry) => {
      val (term, coeff) = entry
      val minterm = Times(coeff, term)
      if (acc == null) minterm else Plus(acc, minterm)
    })
    lhs = if (constTemp.isDefined) {
      if (lhs == null) constTemp.get
      else Plus(lhs, constTemp.get)
    } else lhs
    val expr = oper(Seq(lhs, zero))
    expr
  }

  def templateVars: Set[Variable] = {
    getTemplateVars(template)
  }

  def coeffEntryToString(coeffEntry: (Expr, Expr)): String = {
    val (e, i) = coeffEntry
    i match {
      case InfiniteIntegerLiteral(x) if (x == 1) => e.toString
      case InfiniteIntegerLiteral(x) if (x == -1) => "-" + e.toString
      case InfiniteIntegerLiteral(v) => v + e.toString
      case IntLiteral(1) => e.toString
      case IntLiteral(-1) => "-" + e.toString
      case IntLiteral(v) => v + e.toString
      case _ => i + " * " + e.toString
    }
  }

  override def toExpr: Expr = template

  /**
   * Converts the template to a more human readable form
   * by group positive (and negative) terms together
   */
  def toPrettyExpr = {
    val (lhsCoeff, rhsCoeff) = coeffTemplate.partition {
      case (term, InfiniteIntegerLiteral(v)) =>
        v >= 0
      case _ => true
    }
    var lhsExprs: Seq[Expr] = lhsCoeff.map(e => Times(e._2, e._1)).toSeq
    var rhsExprs: Seq[Expr] = rhsCoeff.map {
      case (term, InfiniteIntegerLiteral(v)) =>
        Times(InfiniteIntegerLiteral(-v), term) // make the coeff +ve
    }.toSeq
    constTemplate match {
      case Some(InfiniteIntegerLiteral(v)) if v < 0 =>
        rhsExprs :+= InfiniteIntegerLiteral(-v)
      case Some(c) =>
        lhsExprs :+= c
      case _ =>
    }
    val lhsExprOpt = ((None: Option[Expr]) /: lhsExprs) {
      case (acc, minterm) =>
        if (acc.isDefined)
          Some(Plus(acc.get, minterm))
        else Some(minterm)
    }
    val rhsExprOpt = ((None: Option[Expr]) /: rhsExprs) {
      case (acc, minterm) =>
        if (acc.isDefined)
          Some(Plus(acc.get, minterm))
        else Some(minterm)
    }
    val lhs = lhsExprOpt.getOrElse(InfiniteIntegerLiteral(0))
    val rhs = rhsExprOpt.getOrElse(InfiniteIntegerLiteral(0))
    oper(Seq(lhs, rhs))
  }

  override def toString(): String = {

    val coeffStr = if (coeffTemplate.isEmpty) ""
    else {
      val (head :: tail) = coeffTemplate.toList
      tail.foldLeft(coeffEntryToString(head))((str, pair) => {

        val termStr = coeffEntryToString(pair)
        (str + " + " + termStr)
      })
    }
    val constStr = if (constTemplate.isDefined) constTemplate.get.toString else ""
    val str = if (!coeffStr.isEmpty() && !constStr.isEmpty()) coeffStr + " + " + constStr
    else coeffStr + constStr
    str + (template match {
      case t: Equals => " = "
      case t: LessThan => " < "
      case t: GreaterThan => " > "
      case t: LessEquals => " <= "
      case t: GreaterEquals => " >= "
    }) + "0"
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

/**
 * class representing a linear constraint. This is a linear template wherein the coefficients are constants
 */
class LinearConstraint(opr: Seq[Expr] => Expr, cMap: Map[Expr, Expr], constant: Option[Expr])
  extends LinearTemplate(opr, cMap, constant) {

  val coeffMap = {
    //assert if the coefficients are only constant expressions
    assert(cMap.values.forall(e => variablesOf(e).isEmpty))
    //TODO: here we should try to simplify the constant expressions
    cMap
  }
  val const = constant.map((c) => {
    //check if constant does not have any variables
    assert(variablesOf(c).isEmpty)
    c
  })
}

case class BoolConstraint(e: Expr) extends Constraint {
  val expr = {
    assert(e match {
      case Variable(_) => true
      case Not(Variable(_)) => true
      case t: BooleanLiteral => true
      case Not(t: BooleanLiteral) => true
      case _ => false
    })
    e
  }
  override def toString(): String = expr.toString
  def toExpr: Expr = expr
}

object ADTConstraint {
  // note: we consider even type parameters as ADT type
  def adtType(e: Expr) = {
    val tpe = e.getType
    tpe.isInstanceOf[ClassType] || tpe.isInstanceOf[TupleType] || tpe.isInstanceOf[TypeParameter]
  }
  def apply(e: Expr): ADTConstraint = e match {    
    case Equals(_: Variable, _: CaseClassSelector | _: TupleSelect) => 
      new ADTConstraint(e, sel = true)    
    case Equals(_: Variable, _: CaseClass | _: Tuple) => 
      new ADTConstraint(e, cons = true)        
    case Equals(_: Variable, _: IsInstanceOf) => 
      new ADTConstraint(e, inst = true) 
    case Equals(lhs @ Variable(_), AsInstanceOf(rhs @ Variable(_), _)) =>       
      new ADTConstraint(Equals(lhs, rhs), comp= true)    
    case Equals(lhs: Variable, _: Variable) if adtType(lhs) =>
      new ADTConstraint(e, comp = true)
    case Not(Equals(lhs: Variable, _: Variable)) if adtType(lhs) => 
      new ADTConstraint(e, comp = true)    
    case _ =>      
      throw new IllegalStateException(s"Expression not an ADT constraint: $e")    
  }
}

class ADTConstraint(val expr: Expr,
  val cons: Boolean = false,
  val inst: Boolean = false,
  val comp: Boolean = false,
  val sel: Boolean = false) extends Constraint { 
  
  override def toString(): String = expr.toString  
  override def toExpr = expr
}

case class Call(retexpr: Expr, fi: FunctionInvocation) extends Constraint {
  val expr = Equals(retexpr, fi)

  override def toExpr = expr
}

object SetConstraint {
  def setConstraintOfBase(e: Expr) = e match {
    case Equals(lhs@Variable(_), _) if lhs.getType.isInstanceOf[SetType] =>
      true
    case Equals(Variable(_), SetUnion(_, _) | FiniteSet(_, _) | ElementOfSet(_, _) | SubsetOf(_, _)) =>
      true
    case _ => false
  }

  def isSetConstraint(e: Expr) = {
    val base = e match {
      case Not(b) => b
      case _ => e
    }
    setConstraintOfBase(base)
  }
}

case class SetConstraint(expr: Expr) extends Constraint {
  var union = false
  var newset = false
  var equal = false
  var elemof = false
  var subset = false
  // TODO: add more operations here
  expr match {
    case Equals(Variable(_), rhs) =>
      rhs match {
        case SetUnion(_, _) => union = true
        case FiniteSet(_, _) => newset = true
        case ElementOfSet(_, _) => elemof = true
        case SubsetOf(_, _) => subset = true
        case Variable(_) => equal = true
      }
  }
  override def toString(): String = {
    expr.toString
  }
  override def toExpr = expr
}

object ConstraintUtil {  

  def createConstriant(ie: Expr): Constraint = {
    ie match {
      case Variable(_) | Not(Variable(_)) | BooleanLiteral(_) | Not(BooleanLiteral(_)) => 
        BoolConstraint(ie)
      case Equals(v @ Variable(_), fi @ FunctionInvocation(_, _)) => 
        Call(v, fi)
      case Equals(_: Variable, _: CaseClassSelector | _: CaseClass | _: TupleSelect | _: Tuple |_: IsInstanceOf) => 
        ADTConstraint(ie)              
      case _ if SetConstraint.isSetConstraint(ie) =>
        SetConstraint(ie)
      // every non-integer equality will be considered an ADT constraint (including TypeParameter equalities)
      case Equals(lhs, rhs) if !isNumericType(lhs.getType) => 
        //println("ADT constraint: "+ie)
        ADTConstraint(ie)      
      case Not(Equals(lhs, rhs)) if !isNumericType(lhs.getType) => 
        ADTConstraint(ie)      
      case _ => {
        val simpe = simplifyArithmetic(ie)
        simpe match {
          case b: BooleanLiteral => BoolConstraint(b)
          case _ => {
            val template = LinearConstraintUtil.exprToTemplate(ie)
            LinearConstraintUtil.evaluate(template) match {
              case Some(v) => BoolConstraint(BooleanLiteral(v))
              case _ => template
            }
          }
        }
      }
    }
  }
}
