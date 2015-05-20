import leon.lang._
import leon.annotation._

object ForElimination { 

  sealed abstract class List
  case class Nil() extends List
  case class Cons(head: Statement, tail: List) extends List

  sealed abstract class Statement 
  case class Print(msg: Int, varID: Int) extends Statement
  case class Assign(varID: Int, expr: Expression) extends Statement
  case class Skip() extends Statement
  case class Block(body: List) extends Statement
  case class IfThenElse(expr: Expression, thenn: Statement, elze: Statement) extends Statement
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
    case IfThenElse(_, thenn, elze) => forLoopsWellFormed(thenn) && forLoopsWellFormed(elze)
    case While(_, body) => forLoopsWellFormed(body)
    case For(init, _, step, body) => isForFree(init) && isForFree(step) && forLoopsWellFormed(body)
    case _ => true
  })

  def eliminateWhileLoopsList(l: List): List = {
    l match {
      case Nil() => Nil()
      case Cons(x, xs) => Cons(eliminateWhileLoops(x), eliminateWhileLoopsList(xs))
    }
  } ensuring(isWhileFreeList(_))

  def eliminateWhileLoops(stat: Statement): Statement = (stat match {
    case Block(body) => Block(eliminateWhileLoopsList(body))
    case IfThenElse(expr, thenn, elze) => IfThenElse(expr, eliminateWhileLoops(thenn), eliminateWhileLoops(elze))
    case While(expr, body) => For(Skip(), expr, Skip(), eliminateWhileLoops(body))
    case For(init, expr, step, body) => For(eliminateWhileLoops(init), expr, eliminateWhileLoops(step), eliminateWhileLoops(body))
    case other => other
  }) ensuring(isWhileFree(_))

  def eliminateForLoopsList(l: List): List = {
    // require(forLoopsWellFormedList(l))
    l match {
      case Nil() => Nil()
      case Cons(x, xs) => Cons(eliminateForLoops(x), eliminateForLoopsList(xs))
    }
  } ensuring(isForFreeList(_))
 
  @induct
  def eliminateForLoops(stat: Statement): Statement = {
    // require(forLoopsWellFormed(stat))
    stat match {
      case Block(body) => Block(eliminateForLoopsList(body))
      case IfThenElse(expr, thenn, elze) => IfThenElse(expr, eliminateForLoops(thenn), eliminateForLoops(elze))
      case While(expr, body) => While(expr, eliminateForLoops(body))
      case For(init, expr, step, body) => Block(Cons(eliminateForLoops(init), Cons(While(expr, Block(Cons(eliminateForLoops(body), Cons(eliminateForLoops(step), Nil())))), Nil())))
      case other => other
    }
  } ensuring(isForFree(_))

  def isWhileFreeList(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, xs) => isWhileFree(x) && isWhileFreeList(xs)
  }

  def isWhileFree(stat: Statement): Boolean = stat match {
    case Block(body) => isWhileFreeList(body)
    case IfThenElse(_, thenn, elze) => isWhileFree(thenn) && isWhileFree(elze)
    case While(_, body) => false
    case For(init,_,step,body) => isWhileFree(init) && isWhileFree(step) && isWhileFree(body)
    case _ => true
  }

  def isForFreeList(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, xs) => isForFree(x) && isForFreeList(xs)
  }
 
  def isForFree(stat: Statement): Boolean = stat match {
    case Block(body) => isForFreeList(body)
    case IfThenElse(_, thenn, elze) => isForFree(thenn) && isForFree(elze)
    case While(_, body) => isForFree(body)
    case For(_,_,_,_) => false
    case _ => true
  }
 
  @induct
  def forFreeEntailsWellFormed(stat: Statement): Boolean = {
    require(isForFree(stat))
    forLoopsWellFormed(stat)
  } // holds

  @induct
  def eliminationIsStable(stat: Statement): Boolean = {
    require(isWhileFree(stat))
    eliminateWhileLoops(stat) == stat
  } holds

}
