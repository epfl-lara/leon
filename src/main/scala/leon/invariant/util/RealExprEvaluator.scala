package leon
package invariant.util

import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import scala.math.BigInt.int2bigInt

object RealValuedExprEvaluator {

  /**
   * Requires that the input expression is ground
   */
  def evaluate(expr: Expr): FractionalLiteral = {
    plainEvaluate(expr)
  }

  def plainEvaluate(expr: Expr): FractionalLiteral = expr match {

    case UMinus(e) => {
      val FractionalLiteral(num, denom) = plainEvaluate(e)
      FractionalLiteral(-num, denom)
    }
    case Minus(lhs, rhs) => {
      plainEvaluate(Plus(lhs, UMinus(rhs)))
    }
    case Plus(_, _) | RealPlus(_, _) => {
      val Operator(Seq(lhs, rhs), op) = expr
      val FractionalLiteral(lnum, ldenom) = plainEvaluate(lhs)
      val FractionalLiteral(rnum, rdenom) = plainEvaluate(rhs)
      normalizeFraction(FractionalLiteral((lnum * rdenom + rnum * ldenom), (ldenom * rdenom)))
    }
    case Times(_, _) | RealTimes(_, _) => {
      val Operator(Seq(lhs, rhs), op) = expr
      val FractionalLiteral(lnum, ldenom) = plainEvaluate(lhs)
      val FractionalLiteral(rnum, rdenom) = plainEvaluate(rhs)
      normalizeFraction(FractionalLiteral((lnum * rnum), (ldenom * rdenom)))
    }
    case Division(_, _) | RealDivision(_, _) => {
      val Operator(Seq(lhs, rhs), op) = expr
      val FractionalLiteral(lnum, ldenom) = plainEvaluate(lhs)
      val FractionalLiteral(rnum, rdenom) = plainEvaluate(rhs)
      plainEvaluate(Times(FractionalLiteral(lnum, ldenom), FractionalLiteral(rdenom, rnum)))
    }
    case il @ InfiniteIntegerLiteral(v) => FractionalLiteral(v, 1)
    case rl @ FractionalLiteral(_, _) => normalizeFraction(rl)
    case _ => throw new IllegalStateException("Not an evaluatable expression: " + expr)
  }

  def evaluateRealPredicate(expr: Expr): Boolean = expr match {
    case Equals(a @ FractionalLiteral(_, _), b @ FractionalLiteral(_, _)) => isEQZ(evaluate(Minus(a, b)))
    case LessEquals(a @ FractionalLiteral(_, _), b @ FractionalLiteral(_, _)) => isLEZ(evaluate(Minus(a, b)))
    case LessThan(a @ FractionalLiteral(_, _), b @ FractionalLiteral(_, _)) => isLTZ(evaluate(Minus(a, b)))
    case GreaterEquals(a @ FractionalLiteral(_, _), b @ FractionalLiteral(_, _)) => isGEZ(evaluate(Minus(a, b)))
    case GreaterThan(a @ FractionalLiteral(n1, d1), b @ FractionalLiteral(n2, d2)) => isGTZ(evaluate(Minus(a, b)))
  }

  def isEQZ(rlit: FractionalLiteral): Boolean = {
    val FractionalLiteral(n, d) = rlit
    if (d == 0) throw new IllegalStateException("denominator zero")
    (n == 0)
  }

  def isLEZ(rlit: FractionalLiteral): Boolean = {
    val FractionalLiteral(n, d) = rlit
    if (d == 0) throw new IllegalStateException("denominator zero")
    if (d < 0) throw new IllegalStateException("denominator negative: " + d)
    (n <= 0)
  }

  def isLTZ(rlit: FractionalLiteral): Boolean = {
    val FractionalLiteral(n, d) = rlit
    if (d == 0) throw new IllegalStateException("denominator zero")
    if (d < 0) throw new IllegalStateException("denominator negative: " + d)
    (n < 0)
  }

  def isGEZ(rlit: FractionalLiteral): Boolean = {
    val FractionalLiteral(n, d) = rlit
    if (d == 0) throw new IllegalStateException("denominator zero")
    if (d < 0) throw new IllegalStateException("denominator negative: " + d)
    (n >= 0)
  }

  def isGTZ(rlit: FractionalLiteral): Boolean = {
    val FractionalLiteral(n, d) = rlit
    if (d == 0) throw new IllegalStateException("denominator zero")
    if (d < 0) throw new IllegalStateException("denominator negative: " + d)
    (n > 0)
  }

  def evaluateRealFormula(expr: Expr): Boolean = expr match {
    case And(args) => args forall evaluateRealFormula
    case Or(args) => args exists evaluateRealFormula
    case Not(arg) => !evaluateRealFormula(arg)
    case BooleanLiteral(b) => b
    case Operator(args, op) =>
      evaluateRealPredicate(op(args map evaluate))
  }
}
