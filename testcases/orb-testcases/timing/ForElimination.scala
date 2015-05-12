import leon.invariant._
import leon.instrumentation._

object ForElimination {

  sealed abstract class List
  case class Nil() extends List
  case class Cons(head: Statement, tail: List) extends List

  sealed abstract class Statement
  case class Print(msg: BigInt, varID: BigInt) extends Statement
  case class Assign(varID: BigInt, expr: Expression) extends Statement
  case class Skip() extends Statement
  case class Block(body: List) extends Statement
  case class IfThenElse(expr: Expression, thenExpr: Statement, elseExpr: Statement) extends Statement
  case class While(expr: Expression, body: Statement) extends Statement
  case class For(init: Statement, expr: Expression, step: Statement, body: Statement) extends Statement

  sealed abstract class Expression
  case class Var(varID: BigInt) extends Expression
  case class IntLiteral(value: BigInt) extends Expression
  case class Plus(lhs: Expression, rhs: Expression) extends Expression
  case class Minus(lhs: Expression, rhs: Expression) extends Expression
  case class Times(lhs: Expression, rhs: Expression) extends Expression
  case class Division(lhs: Expression, rhs: Expression) extends Expression
  case class Equals(lhs: Expression, rhs: Expression) extends Expression
  case class LessThan(lhs: Expression, rhs: Expression) extends Expression
  case class And(lhs: Expression, rhs: Expression) extends Expression
  case class Or(lhs: Expression, rhs: Expression) extends Expression
  case class Not(expr: Expression) extends Expression

  def sizeStat(st: Statement) : BigInt =  st match {
    case Block(l) => sizeList(l) + 1
    case IfThenElse(c,th,el) => sizeStat(th) + sizeStat(el) + 1
    case While(c,b) => sizeStat(b) + 1
    case For(init,cond,step,body) => sizeStat(init) + sizeStat(step) + sizeStat(body)
    case other => 1
  }

  def sizeList(l: List) : BigInt = l match {
    case Cons(h,t) => sizeStat(h) + sizeList(t)
    case Nil() => 0
  }

  def isForFree(stat: Statement): Boolean = (stat match {
    case Block(body) => isForFreeList(body)
    case IfThenElse(_, thenExpr, elseExpr) => isForFree(thenExpr) && isForFree(elseExpr)
    case While(_, body) => isForFree(body)
    case For(_,_,_,_) => false
    case _ => true
  })  ensuring(res => true && tmpl((a,b) => time <= a*sizeStat(stat) + b))

  def isForFreeList(l: List): Boolean = (l match {
    case Nil() => true
    case Cons(x, xs) => isForFree(x) && isForFreeList(xs)
  })  ensuring(res => true && tmpl((a,b) => time <= a*sizeList(l) + b))

  def forLoopsWellFormedList(l: List): Boolean = (l match {
    case Nil() => true
    case Cons(x, xs) => forLoopsWellFormed(x) && forLoopsWellFormedList(xs)
  }) ensuring(res => true && tmpl((a,b) => time <= a*sizeList(l) + b))

  def forLoopsWellFormed(stat: Statement): Boolean = (stat match {
    case Block(body) => forLoopsWellFormedList(body)
    case IfThenElse(_, thenExpr, elseExpr) => forLoopsWellFormed(thenExpr) && forLoopsWellFormed(elseExpr)
    case While(_, body) => forLoopsWellFormed(body)
    case For(init, _, step, body) => isForFree(init) && isForFree(step) && forLoopsWellFormed(body)
    case _ => true
  }) ensuring(res => true && tmpl((a,b) => time <= a*sizeStat(stat) + b))

  def eliminateWhileLoopsList(l: List): List = {
    l match {
      case Nil() => Nil()
      case Cons(x, xs) => Cons(eliminateWhileLoops(x), eliminateWhileLoopsList(xs))
    }
  } ensuring(res => true && tmpl((a,b) => time <= a*sizeList(l) + b))

  def eliminateWhileLoops(stat: Statement): Statement = (stat match {
    case Block(body) => Block(eliminateWhileLoopsList(body))
    case IfThenElse(expr, thenExpr, elseExpr) => IfThenElse(expr, eliminateWhileLoops(thenExpr), eliminateWhileLoops(elseExpr))
    case While(expr, body) => For(Skip(), expr, Skip(), eliminateWhileLoops(body))
    case For(init, expr, step, body) => For(eliminateWhileLoops(init), expr, eliminateWhileLoops(step), eliminateWhileLoops(body))
    case other => other
  }) ensuring(res => true && tmpl((a,b) => time <= a*sizeStat(stat) + b))

  def eliminateForLoopsList(l: List): List = {
    l match {
      case Nil() => Nil()
      case Cons(x, xs) => Cons(eliminateForLoops(x), eliminateForLoopsList(xs))
    }
  } ensuring(res => true && tmpl((a,b) => time <= a*sizeList(l) + b))

  def eliminateForLoops(stat: Statement): Statement = {
    stat match {
      case Block(body) => Block(eliminateForLoopsList(body))
      case IfThenElse(expr, thenExpr, elseExpr) => IfThenElse(expr, eliminateForLoops(thenExpr), eliminateForLoops(elseExpr))
      case While(expr, body) => While(expr, eliminateForLoops(body))
      case For(init, expr, step, body) => Block(Cons(eliminateForLoops(init), Cons(While(expr, Block(Cons(eliminateForLoops(body), Cons(eliminateForLoops(step), Nil())))), Nil())))
      case other => other
    }
  } ensuring(res => true && tmpl((a,b) => time <= a*sizeStat(stat) + b))
}
