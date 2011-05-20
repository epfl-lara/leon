import cp.Definitions._

@spec object Specs {
  sealed abstract class Nat
  case class Zero() extends Nat
  case class Succ(n : Nat) extends Nat

  def natValue(nat : Nat) : Int = (nat match {
    case Zero() => 0
    case Succ(n) => 1 + natValue(n)
  }) ensuring(_ >= 0)

  sealed abstract class Token
  case class IntLit(value : Nat) extends Token
  case class Plus() extends Token
  case class Minus() extends Token
  case class Times() extends Token
  case class Div() extends Token

  sealed abstract class TokenList
  case class Cons(head : Token, tail : TokenList) extends TokenList
  case class Nil() extends TokenList

  def size(l : TokenList) : Int = (l match {
    case Nil() => 0
    case Cons(x, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def append(l1 : TokenList, l2 : TokenList) : TokenList = (l1 match {
    case Nil() => l2
    case Cons(t, ts) => Cons(t, append(ts, l2))
  }) ensuring(size(_) == size(l1) + size(l2))
  
  sealed abstract class Tree
  case class IntLitTree(value : Nat) extends Tree
  case class PlusTree(left : Tree, right : Tree) extends Tree
  case class MinusTree(left : Tree, right : Tree) extends Tree
  case class TimesTree(left : Tree, right : Tree) extends Tree
  case class DivTree(left : Tree, right : Tree) extends Tree

  def treeSize(t : Tree) : Int = (t match {
    case IntLitTree(_) => 1
    case PlusTree(l,r) => 1 + treeSize(l) + treeSize(r)
    case MinusTree(l,r) => 1 + treeSize(l) + treeSize(r)
    case TimesTree(l,r) => 1 + treeSize(l) + treeSize(r)
    case DivTree(l,r) => 1 + treeSize(l) + treeSize(r)
  }) ensuring(_ >= 0)

  def print(tree : Tree) : TokenList = tree match {
    case IntLitTree(value) => Cons(IntLit(value), Nil())
    case PlusTree(l, r) => append(print(l), Cons(Plus(), print(r)))
    case MinusTree(l, r) => append(print(l), Cons(Minus(), print(r)))
    case TimesTree(l, r) => append(print(l), Cons(Times(), print(r)))
    case DivTree(l, r) => append(print(l), Cons(Div(), print(r)))
  }

  /*
  def valuesBoundedBy(tree : Tree, nat : Nat) : Boolean = tree match {
    
  }
  */
}

object Parser {
  import Specs._

  implicit def int2nat(i : Int) : Nat = if (i <= 0) Zero() else Succ(int2nat(i-1))

  def main(args : Array[String]) : Unit = {
    // val tokens = Cons(IntLit(42), Cons(Plus(), Cons(IntLit(43), Cons(Times(), Cons(IntLit(44), Nil())))))
    val tokens = Cons(IntLit(1), Cons(Plus(), Cons(IntLit(2), Nil())))
    val tree = ((t : Tree) => print(t) == tokens).solve
    println("The tree I found: " + tree)

    println("Printing : " + print(tree))
  }
}
