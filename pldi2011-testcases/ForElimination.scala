import scala.collection.immutable.Set
import funcheck.Utils._
import funcheck.Annotations._

object ForElimination { 

  sealed abstract class List
  case class Nil() extends List
  case class Cons(head: Statement, tail: List) extends List

  sealed abstract class Statement 
  case class Print(msg: Int, varID: Int) extends Statement
  case class Assign(varID: Int, expr: Expression) extends Statement
  case class Skip() extends Statement
  case class Block(body: List) extends Statement
  case class IfThenElse(expr: Expression, then: Statement, elze: Statement) extends Statement
  case class While(expr: Expression, body: Statement) extends Statement
  case class For(init: Statement, expr: Expression, step: Statement, body: Statement) extends Statement

  sealed abstract class Expression 
  case class Var(varID: Int) extends Expression
  case class IntLiteral(value: Int) extends Expression
  case class Plus(lhs: Expression, rhs: Expression) extends Expression
  case class Minus(lhs: Expression, rhs: Expression) extends Expression
  case class Times(lhs: Expression, rhs: Expression) extends Expression
  case class Division(lhs: Expression, rhs: Expression) extends Expression
  case class Modulo(lhs: Expression, rhs: Expression) extends Expression
  case class Equals(lhs: Expression, rhs: Expression) extends Expression
  case class GreaterThan(lhs: Expression, rhs: Expression) extends Expression
  case class LessThan(lhs: Expression, rhs: Expression) extends Expression
  case class And(lhs: Expression, rhs: Expression) extends Expression
  case class Or(lhs: Expression, rhs: Expression) extends Expression
  case class Neg(expr: Expression) extends Expression
  case class Not(expr: Expression) extends Expression

  def forLoopsWellFormedList(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, xs) => forLoopsWellFormed(x) && forLoopsWellFormedList(xs)
  }

  def forLoopsWellFormed(stat: Statement): Boolean = (stat match {
    case Block(body) => forLoopsWellFormedList(body)
    case IfThenElse(_, then, elze) => forLoopsWellFormed(then) && forLoopsWellFormed(elze)
    case While(_, body) => forLoopsWellFormed(body)
    case For(init, _, step, body) => isForFree(init) && isForFree(step) && forLoopsWellFormed(body)
    case _ => true
  })

  def eliminateForLoopsList(l: List): List = {
    require(forLoopsWellFormedList(l))
    l match {
      case Nil() => Nil()
      case Cons(x, xs) => Cons(eliminateForLoops(x), eliminateForLoopsList(xs))
    }
  } ensuring(isForFreeList(_))

  @induct
  def eliminateForLoops(stat: Statement): Statement = {
    require(forLoopsWellFormed(stat))
    stat match {
      case Block(body) => Block(eliminateForLoopsList(body))
      case IfThenElse(expr, then, elze) => IfThenElse(expr, eliminateForLoops(then), eliminateForLoops(elze))
      case While(expr, body) => While(expr, eliminateForLoops(body))
      case For(init, expr, step, body) => Block(Cons(init, Cons(While(expr, Block(Cons(eliminateForLoops(body), Cons(step, Nil())))), Nil())))
      case other => other
    }
  } ensuring(isForFree(_))

  def isForFreeList(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, xs) => isForFree(x) && isForFreeList(xs)
  }

  def isForFree(stat: Statement): Boolean = stat match {
    case Block(body) => isForFreeList(body)
    case IfThenElse(_, then, elze) => isForFree(then) && isForFree(elze)
    case While(_, body) => isForFree(body)
    case For(_,_,_,_) => false
    case _ => true
  }

  @induct
  def forFreeEntailsWellFormed(stat: Statement): Boolean = {
    require(isForFree(stat))
    forLoopsWellFormed(stat)
  } holds

  @induct
  def eliminationIsStable(stat: Statement): Boolean = {
    require(isForFree(stat))
    eliminateForLoops(stat) == stat
  } holds

}
