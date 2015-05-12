package leon
package invariant.structure

import z3.scala._
import purescala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import solvers.{ Solver, TimeoutSolver }
import solvers.z3.FairZ3Solver
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.mutable.{ Map => MutableMap }
import evaluators._
import java.io._
import solvers.z3.UninterpretedZ3Solver
import invariant.util._

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
    assert(coeffTemp.values.foldLeft(true)((acc, e) => {
      acc && Util.isTemplateExpr(e)
    }))

    //print the template mapping
    /*println("Coeff Mapping: "+coeffTemp)
    println("Constant: "+constTemplate)*/
    coeffTemp
  }

  val constTemplate = {
    assert(constTemp match {
      case None => true
      case Some(e) => Util.isTemplateExpr(e)
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
    //assert(expr.isInstanceOf[Equals] || expr.isInstanceOf[LessThan] || expr.isInstanceOf[GreaterThan]
    //  || expr.isInstanceOf[LessEquals] || expr.isInstanceOf[GreaterEquals])
    expr
  }

  def templateVars: Set[Variable] = {
    Util.getTemplateVars(template)
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
    assert(cMap.values.foldLeft(true)((acc, e) => {
      acc && variablesOf(e).isEmpty
    }))

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

  override def toString(): String = {
    expr.toString
  }

  def toExpr: Expr = expr
}

object ADTConstraint {

  def apply(e: Expr): ADTConstraint = e match {

    //is this a tuple or case class select ?
    // case Equals(Variable(_), CaseClassSelector(_, _, _)) | Iff(Variable(_), CaseClassSelector(_, _, _)) => {
    case Equals(Variable(_), CaseClassSelector(_, _, _)) => {
      val ccExpr = ExpressionTransformer.classSelToCons(e)
      new ADTConstraint(ccExpr, Some(ccExpr))
    }
    // case Equals(Variable(_),TupleSelect(_,_)) | Iff(Variable(_),TupleSelect(_,_)) => {
    case Equals(Variable(_), TupleSelect(_, _)) => {
      val tpExpr = ExpressionTransformer.tupleSelToCons(e)
      new ADTConstraint(tpExpr, Some(tpExpr))
    }
    //is this a tuple or case class def ?
    case Equals(Variable(_), CaseClass(_, _)) | Equals(Variable(_), Tuple(_)) => {
      new ADTConstraint(e, Some(e))
    }
    //is this an instanceOf ?
    case Equals(v @ Variable(_), ci @ IsInstanceOf(_, _)) => {
      new ADTConstraint(e, None, Some(e))
    }
    // considering asInstanceOf as equalities
    case Equals(lhs @ Variable(_), ci @ AsInstanceOf(rhs @ Variable(_), _)) => {
      val eq = Equals(lhs, rhs)
      new ADTConstraint(eq, None, None, Some(eq))
    }
    //equals and disequalities betweeen variables
    case Equals(lhs @ Variable(_), rhs @ Variable(_)) if (lhs.getType != Int32Type && lhs.getType != RealType && lhs.getType != IntegerType) => {
      new ADTConstraint(e, None, None, Some(e))
    }
    case Not(Equals(lhs @ Variable(_), rhs @ Variable(_))) if (lhs.getType != Int32Type && lhs.getType != RealType && lhs.getType != IntegerType) => {
      new ADTConstraint(e, None, None, Some(e))
    }
    case _ => {
      throw new IllegalStateException("Expression not an ADT constraint: " + e)
    }
  }
}

class ADTConstraint(val expr: Expr,
  val cons: Option[Expr] = None,
  val inst: Option[Expr] = None,
  val comp: Option[Expr] = None) extends Constraint {

  override def toString(): String = {
    expr.toString
  }

  override def toExpr = expr
}

case class Call(retexpr: Expr, fi: FunctionInvocation) extends Constraint {
  val expr = Equals(retexpr, fi)

  override def toExpr = expr
}

object ConstraintUtil {

  def createConstriant(ie: Expr): Constraint = {
    ie match {
      case Variable(_) | Not(Variable(_)) | BooleanLiteral(_) | Not(BooleanLiteral(_)) => BoolConstraint(ie)
      case Equals(v @ Variable(_), fi @ FunctionInvocation(_, _)) => Call(v, fi)
      case Equals(Variable(_), CaseClassSelector(_, _, _))
        | Equals(Variable(_), CaseClass(_, _))
        | Equals(Variable(_), TupleSelect(_, _))
        | Equals(Variable(_), Tuple(_))
        | Equals(Variable(_), IsInstanceOf(_, _)) => {

        ADTConstraint(ie)
      }
      case Equals(lhs, rhs) if (lhs.getType != Int32Type && lhs.getType != RealType && lhs.getType != IntegerType) => {
        //println("ADT constraint: "+ie)
        ADTConstraint(ie)
      }
      case Not(Equals(lhs, rhs)) if (lhs.getType != Int32Type && lhs.getType != RealType && lhs.getType != IntegerType) => {
        ADTConstraint(ie)
      }
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
