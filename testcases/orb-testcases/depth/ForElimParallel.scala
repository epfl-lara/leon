import leon.instrumentation._
import leon.invariant._


object ForElimination {

  sealed abstract class Tree
  case class Node(left: Tree, value: Statement, right: Tree) extends Tree
  case class Leaf() extends Tree

  sealed abstract class Statement
  case class Print(msg: BigInt, varID: BigInt) extends Statement
  case class Assign(varID: BigInt, expr: Expression) extends Statement
  case class Skip() extends Statement
  case class Block(body: Tree) extends Statement
  case class IfThenElse(expr: Expression, then: Statement, elze: Statement) extends Statement
  case class While(expr: Expression, body: Statement) extends Statement
  case class For(init: Statement, expr: Expression, step: Statement, body: Statement) extends Statement

  sealed abstract class Expression
  case class Var(varID: BigInt) extends Expression
  case class BigIntLiteral(value: BigInt) extends Expression
  case class Plus(lhs: Expression, rhs: Expression) extends Expression
  case class Minus(lhs: Expression, rhs: Expression) extends Expression
  case class Times(lhs: Expression, rhs: Expression) extends Expression
  case class Division(lhs: Expression, rhs: Expression) extends Expression
  case class Equals(lhs: Expression, rhs: Expression) extends Expression
  case class LessThan(lhs: Expression, rhs: Expression) extends Expression
  case class And(lhs: Expression, rhs: Expression) extends Expression
  case class Or(lhs: Expression, rhs: Expression) extends Expression
  case class Not(expr: Expression) extends Expression

  /*def sizeStat(st: Statement) : BigInt =  st match {
    case Block(l) => sizeList(l) + 1
    case IfThenElse(c,th,el) => sizeStat(th) + sizeStat(el) + 1
    case While(c,b) => sizeStat(b) + 1
    case For(init,cond,step,body) => sizeStat(init) + sizeStat(step) + sizeStat(body)
    case other => 1
  }

  def sizeTree(l: List) : BigInt = l match {
    case Node(l,x,r) => sizeTree(l) + sizeTree(r) + sizeStat(x)
    case Nil() => 0
  }*/

  def max(x: BigInt, y: BigInt) = if(x >= y) x else y

  def depthStat(st: Statement) : BigInt =  st match {
    case Block(t) => depthTree(t) + 1
    case IfThenElse(c,th,el) => max(depthStat(th),depthStat(el)) + 1
    case While(c,b) => depthStat(b) + 1
    case For(init,cond,step,body) => max(max(depthStat(init),depthStat(step)),depthStat(body))
    case other => 1
  }

  def depthTree(t: Tree) : BigInt = t match {
    case Node(l,x,r) => max(max(depthTree(l),depthTree(r)),depthStat(x)) + 1
    case Leaf() => 0
  }

  /*def isForFree(stat: Statement): Boolean = (stat match {
    case Block(body) => isForFreeTree(body)
    case IfThenElse(_, then, elze) => isForFree(then) && isForFree(elze)
    case While(_, body) => isForFree(body)
    case For(_,_,_,_) => false
    case _ => true
  })  ensuring(res => true && tmpl((a,b) => depth <= a*depthStat(stat) + b))

  def isForFreeTree(t: Tree): Boolean = (t match {
    case Leaf() => true
    case Node(l, x, r) => isForFree(x) && isForFreeTree(l) && isForFreeTree(r)
  })  ensuring(res => true && tmpl((a,b) => depth <= a*depthTree(t) + b))*/

  /*def forLoopsWellFormedTree(t: Tree): Boolean = (t match {
    case Leaf() => true
    case Node(l, x, r) => forLoopsWellFormed(x) && forLoopsWellFormedTree(l) && forLoopsWellFormedTree(r)
  }) ensuring(res => true && tmpl((a,b) => depth <= a*depthTree(t) + b))

  def forLoopsWellFormed(stat: Statement): Boolean = (stat match {
    case Block(body) => forLoopsWellFormedTree(body)
    case IfThenElse(_, then, elze) => forLoopsWellFormed(then) && forLoopsWellFormed(elze)
    case While(_, body) => forLoopsWellFormed(body)
    case For(init, _, step, body) => isForFree(init) && isForFree(step) && forLoopsWellFormed(body)
    case _ => true
  }) ensuring(res => true && tmpl((a,b) => depth <= a*depthStat(stat) + b))*/

  def eliminateWhileLoopsTree(t: Tree): Tree = {
    t match {
      case Leaf() => Leaf()
      case Node(l,x,r) => Node(eliminateWhileLoopsTree(l), eliminateWhileLoops(x), eliminateWhileLoopsTree(r))
    }
  } ensuring(res => true && tmpl((a,b) => depth <= a*depthTree(t) + b))

  def eliminateWhileLoops(stat: Statement): Statement = (stat match {
    case Block(body) => Block(eliminateWhileLoopsTree(body))
    case IfThenElse(expr, then, elze) => IfThenElse(expr, eliminateWhileLoops(then), eliminateWhileLoops(elze))
    case While(expr, body) => For(Skip(), expr, Skip(), eliminateWhileLoops(body))
    case For(init, expr, step, body) => For(eliminateWhileLoops(init), expr, eliminateWhileLoops(step), eliminateWhileLoops(body))
    case other => other
  }) ensuring(res => true && tmpl((a,b) => depth <= a*depthStat(stat) + b))

  /*def eliminateForLoopsTree(t: Tree): Tree = {
    t match {
      case Leaf() => Leaf()
      case Node(l,x,r) => Node(eliminateForLoopsTree(l), eliminateForLoops(x), eliminateForLoopsTree(r))
    }
  } ensuring(res => true && tmpl((a,b) => depth <= a*depthTree(t) + b))

  def eliminateForLoops(stat: Statement): Statement = {
    stat match {
      case Block(body) => Block(eliminateForLoopsTree(body))
      case IfThenElse(expr, then, elze) => IfThenElse(expr, eliminateForLoops(then), eliminateForLoops(elze))
      case While(expr, body) => While(expr, eliminateForLoops(body))
      case For(init, expr, step, body) => Block(Node(Leaf(),eliminateForLoops(init),Node(Leaf(),
          While(expr, Block(Node(Leaf(),eliminateForLoops(body), Node(Leaf(),eliminateForLoops(step), Leaf())))),Leaf())))
      case other => other
    }
  } ensuring(res => true && tmpl((a,b) => depth <= a*depthStat(stat) + b))*/
}
