import leon.lang._
import leon.collection._

object Transformation {
  
  abstract class Expr
  case class If(cond: Expr, t: Expr, e: Expr) extends Expr
  case class Add(e1: Expr, e2: Expr) extends Expr
  case class Equals(e1: Expr, e2: Expr) extends Expr
  case class Literal(i: BigInt) extends Expr

  def transform(f: Expr => Option[Expr])(expr: Expr): Expr = {
    val rec = (x: Expr) => transform(f)(x)
    val newExpr = expr match {
      case If(cond, t, e) => If(rec(cond), rec(t), rec(e))
      case Add(e1, e2) => Add(rec(e1), rec(e2))
      case Equals(e1, e2) => Equals(rec(e1), rec(e2))
      case Literal(i) => Literal(i)
    }

    f(newExpr) match {
      case Some(e) => e
      case None() => newExpr
    }
  }

  def exists(f: Expr => Boolean)(expr: Expr): Boolean = {
    val rec = (x: Expr) => exists(f)(x)
    f(expr) || (expr match {
      case If(cond, t, e) => rec(cond) || rec(t) || rec(e)
      case Add(e1, e2) => rec(e1) || rec(e2)
      case Equals(e1, e2) => rec(e1) || rec(e2)
      case Literal(i) => false
    })
  }

  def test(expr: Expr) = {
    val t = transform(e => e match {
      case Equals(Add(Literal(i), Literal(j)), e2) => Some(Equals(Literal(i + j), e2))
      case Equals(e1, Add(Literal(i), Literal(j))) => Some(Equals(e1, Literal(i + j)))
      case _ => None[Expr]()
    })(expr)

    !exists(e => e match {
      case Equals(_, Add(Literal(i), Literal(j))) => true
      case _ => false
    })(t)
  }.holds
}
