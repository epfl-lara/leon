import cp.Definitions._

@spec object Specs {
  sealed abstract class Bool
  case class True() extends Bool
  case class False() extends Bool

  sealed abstract class Token
  case class BooleanLit(value : Bool) extends Token
  case class And() extends Token
  case class Or() extends Token
  case class Implies() extends Token
  case class LParen() extends Token
  case class RParen() extends Token

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
  case class BooleanLitTree(value : Bool) extends Tree
  case class AndTree(left : Tree, right : Tree) extends Tree
  case class OrTree(left : Tree, right : Tree) extends Tree
  case class ImpliesTree(left : Tree, right : Tree) extends Tree

  def treeSize(t : Tree) : Int = (t match {
    case BooleanLitTree(_) => 1
    case AndTree(l,r) => 1 + treeSize(l) + treeSize(r)
    case OrTree(l,r) => 1 + treeSize(l) + treeSize(r)
    case ImpliesTree(l,r) => 1 + treeSize(l) + treeSize(r)
  }) ensuring(_ >= 0)

  def enclose(l : TokenList) : TokenList =
    append(Cons(LParen(), l), Cons(RParen(), Nil()))

  def print(tree : Tree) : TokenList = tree match {
    case BooleanLitTree(value) => Cons(BooleanLit(value), Nil())
    case AndTree(l, r) => append(print(l), Cons(And(), print(r)))
    case OrTree(l, r) => append(print(l), Cons(Or(), print(r)))
    case ImpliesTree(l, r) => append(print(l), Cons(Implies(), print(r)))
  }

  def printAlternative(tree : Tree, acc : TokenList) : TokenList = tree match {
    case BooleanLitTree(value) => Cons(BooleanLit(value), acc)
    case AndTree(l, r) => printAlternative(l, Cons(And(), printAlternative(r, acc)))
    case OrTree(l, r) => printAlternative(l, Cons(Or(), printAlternative(r, acc)))
    case ImpliesTree(l, r) => printAlternative(l, Cons(Implies(), printAlternative(r, acc)))
  }
}

object PropositionalLogicParser {
  import Specs._

  implicit def scalaList2list(l : List[Token]) : TokenList = l match {
    case scala.collection.immutable.Nil => Nil()
    case t :: ts => Cons(t, scalaList2list(ts))
  }

  def main(args : Array[String]) : Unit = {
    // val tokens : TokenList = List[Token](BooleanLit(False()), And(), BooleanLit(True()), And(), BooleanLit(True()))
    val tokens : TokenList = List[Token](BooleanLit(False()), Or(), BooleanLit(True()))
    val tree = ((t : Tree) => print(t) == tokens).solve

    println("The tree I found: " + tree)
    println("Printing : " + print(tree))
  }
}
