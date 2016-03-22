/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.structure

import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import invariant.util._
import Util._
import PredicateUtil._
import TypeUtil._
import purescala.Extractors._
import ExpressionTransformer._
import solvers.Model
import purescala.Common._
import leon.evaluators._

trait Constraint {
  def toExpr: Expr
}

trait ExtendedConstraint extends Constraint {
  def pickSatDisjunct(model: LazyModel, tmplModel: Map[Identifier,Expr], eval: DefaultEvaluator): Constraint
}

object LinearTemplate {
   val debug = false
   val debugPickSat = false
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

  import LinearTemplate._

  val zero = InfiniteIntegerLiteral(0)
  val op = oper

  val coeffTemplate = {
    if(debug) assert(coeffTemp.values.forall(e => isTemplateExpr(e)))
    coeffTemp
  }

  val constTemplate = {
    if(debug) assert(constTemp.map(isTemplateExpr).getOrElse(true))
    constTemp
  }

  val lhsExpr = {
    //construct the expression corresponding to the template here
    var lhs = coeffTemp.foldLeft(null: Expr) {
      case (acc, (term, coeff)) =>
        val minterm = Times(coeff, term)
        if (acc == null) minterm else Plus(acc, minterm)
    }
    if (constTemp.isDefined) {
      if (lhs == null) constTemp.get
      else Plus(lhs, constTemp.get)
    } else lhs
  }

  val template = oper(Seq(lhsExpr, zero))

  def templateVars: Set[Variable] = getTemplateVars(template)  

  /**
   * Picks a sat disjunct of the negation of the template w.r.t to the
   * given model.
   */
  lazy val negTmpls = {
    val args = template match {
      case _: Equals => Seq(GreaterThan(lhsExpr, zero), LessThan(lhsExpr,zero))
      case _: LessEquals => Seq(GreaterThan(lhsExpr, zero))
      case _: LessThan => Seq(GreaterEquals(lhsExpr, zero))
      case _: GreaterEquals => Seq(LessThan(lhsExpr, zero))
      case _: GreaterThan => Seq(LessEquals(lhsExpr, zero))
    }
    args map LinearConstraintUtil.exprToTemplate
  }
  
  def pickSatDisjunctOfNegation(model: LazyModel, tmplModel: Map[Identifier, Expr], eval: DefaultEvaluator) = {
    val err = new IllegalStateException(s"Cannot pick a sat disjunct of negation: ${toString} is sat!")
    template match {
      case _: Equals => // here, negation is a disjunction
        UnflatHelper.evaluate(replaceFromIDs(tmplModel, lhsExpr), model, eval) match {
          case InfiniteIntegerLiteral(lval) =>
            val Seq(grt, less) = negTmpls
            if (lval > 0) grt
            else if (lval < 0) less
            else throw err
        }
      case _ => // here, the negation must be sat
        if (debugPickSat) {
          if (UnflatHelper.evaluate(replaceFromIDs(tmplModel, negTmpls.head.toExpr), model, eval) != tru)
            throw err
        }
        negTmpls.head
    }
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

  override def hashCode(): Int = template.hashCode()

  override def equals(obj: Any): Boolean = obj match {
    case lit: LinearTemplate => lit.template.equals(this.template)
    case _ => false
  }
}

/**
 * class representing a linear constraint. This is a linear template wherein the coefficients are constants
 */
class LinearConstraint(opr: Seq[Expr] => Expr, cMap: Map[Expr, Expr], constant: Option[Expr])
  extends LinearTemplate(opr, cMap, constant) {
  val coeffMap = cMap
  val const = constant
}

/**
 * Class representing Equality or disequality of a boolean variable and an linear template.
 * Used for efficiently choosing a disjunct
 */
case class ExtendedLinearTemplate(v: Variable, tmpl: LinearTemplate, diseq: Boolean) extends ExtendedConstraint {
  val expr = {
    val eqExpr = Equals(v, tmpl.toExpr)
    if(diseq) Not(eqExpr) else eqExpr
  }
  override def toExpr = expr
  override def toString: String = expr.toString

  /**
   * Chooses a sat disjunct of the constraint
   */
  override def pickSatDisjunct(model: LazyModel, tmplModel: Map[Identifier,Expr], eval: DefaultEvaluator) = {
    if((model(v.id) == tru && !diseq) || (model(v.id) == fls && diseq)) tmpl
    else {
      //println(s"Picking sat disjunct of: ${toExpr} model($v) = ${model(v.id)}")
      tmpl.pickSatDisjunctOfNegation(model, tmplModel, eval)
    }
  }
}

object BoolConstraint {
  def isBoolConstraint(e: Expr): Boolean = e match {
    case _: Variable | _: BooleanLiteral if e.getType == BooleanType => true
    case Equals(l, r) => isBoolConstraint(l) && isBoolConstraint(r) //enabling makes the system slower!! surprising
    case Not(arg) => isBoolConstraint(arg)
    case And(args) => args forall isBoolConstraint
    case Or(args) => args forall isBoolConstraint
    case _ => false
  }
}

case class BoolConstraint(e: Expr) extends Constraint {
  import BoolConstraint._
  val expr = {
    assert(isBoolConstraint(e))
    e
  }
  override def toString(): String = expr.toString
  def toExpr: Expr = expr
}

object ADTConstraint {
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

case class ExtendedADTConstraint(v: Variable, adtCtr: ADTConstraint, diseq: Boolean) extends ExtendedConstraint {
  val expr = {
    assert(adtCtr.comp)
    val eqExpr = Equals(v, adtCtr.toExpr)
    if(diseq) Not(eqExpr) else eqExpr
  }
  override def toExpr = expr
  override def toString: String = expr.toString

  /**
   * Chooses a sat disjunct of the constraint
   */
  override def pickSatDisjunct(model: LazyModel, tmplModel: Map[Identifier,Expr], eval: DefaultEvaluator) = {
    if((model(v.id) == tru && !diseq) || (model(v.id) == fls && diseq)) adtCtr
    else ADTConstraint(Not(adtCtr.toExpr))
  }
}

case class Call(retexpr: Expr, fi: FunctionInvocation) extends Constraint {
  val expr = Equals(retexpr, fi)
  override def toExpr = expr
}

/**
 * If-then-else constraint
 */
case class ITE(cond: BoolConstraint, ths: Seq[Constraint], elzs: Seq[Constraint]) extends Constraint {
  val expr = IfExpr(cond.toExpr, createAnd(ths.map(_.toExpr)), createAnd(elzs.map(_.toExpr)))
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
  def toLinearTemplate(ie: Expr) = {
    simplifyArithmetic(ie) match {
      case b: BooleanLiteral => BoolConstraint(b)
      case _ => {
        val template = LinearConstraintUtil.exprToTemplate(ie)
        LinearConstraintUtil.evaluate(template) match {
          case Some(v) => BoolConstraint(BooleanLiteral(v))
          case _       => template
        }
      }
    }
  }

  def toExtendedTemplate(v: Variable, ie: Expr, diseq: Boolean) = {
    toLinearTemplate(ie) match {
      case bc: BoolConstraint => BoolConstraint(Equals(v, bc.toExpr))
      case t: LinearTemplate  => ExtendedLinearTemplate(v, t, diseq)
    }
  }

  def createConstriant(ie: Expr): Constraint = {
    ie match {
      case _ if BoolConstraint.isBoolConstraint(ie)               => BoolConstraint(ie)
      case Equals(v @ Variable(_), fi @ FunctionInvocation(_, _)) => Call(v, fi)
      case Equals(_: Variable, _: CaseClassSelector | _: CaseClass | _: TupleSelect | _: Tuple | _: IsInstanceOf) =>
        ADTConstraint(ie)
      case _ if SetConstraint.isSetConstraint(ie)                                      => SetConstraint(ie)
      case Equals(v: Variable, rhs) if (isArithmeticRelation(rhs) != Some(false))      => toExtendedTemplate(v, rhs, false)
      case Not(Equals(v: Variable, rhs)) if (isArithmeticRelation(rhs) != Some(false)) => toExtendedTemplate(v, rhs, true)
      case _ if (isArithmeticRelation(ie) != Some(false))                              => toLinearTemplate(ie)
      case Equals(v: Variable, rhs@Equals(l, _)) if adtType(l) => ExtendedADTConstraint(v, ADTConstraint(rhs), false)

      // every other equality will be considered an ADT constraint (including TypeParameter equalities)
      case Equals(lhs, rhs) if !isNumericType(lhs.getType)                             => ADTConstraint(ie)
      case Not(Equals(lhs, rhs)) if !isNumericType(lhs.getType)                        => ADTConstraint(ie)
    }
  }
}
