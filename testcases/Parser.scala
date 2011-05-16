object Parser {
  sealed abstract class Token
  case class IntLit(value : Boolean) extends Token
  case class Plus() extends Token
  case class Minus() extends Token
  case class Times() extends Token
  case class Div() extends Token
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
  case class IntLitTree(value : Boolean) extends Tree
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

  def enclose(l : TokenList) : TokenList =
    append(Cons(LParen(), l), Cons(RParen(), Nil()))

  def print(tree : Tree) : TokenList = tree match {
    case IntLitTree(value) => Cons(IntLit(value), Nil())
    case PlusTree(l, r) => append(print(l), Cons(Plus(), print(r)))
    case MinusTree(l, r) => append(print(l), Cons(Minus(), print(r)))
    case TimesTree(l, r) => append(print(l), Cons(Times(), print(r)))
    case DivTree(l, r) => append(print(l), Cons(Div(), print(r)))
  }

  def printAlternative(tree : Tree, acc : TokenList) : TokenList = tree match {
    case IntLitTree(value) => Cons(IntLit(value), acc)
    case PlusTree(l, r) => printAlternative(l, Cons(Plus(), printAlternative(r, acc)))
    case MinusTree(l, r) => printAlternative(l, Cons(Minus(), printAlternative(r, acc)))
    case TimesTree(l, r) => printAlternative(l, Cons(Times(), printAlternative(r, acc)))
    case DivTree(l, r) => printAlternative(l, Cons(Div(), printAlternative(r, acc)))
  }

  def findTree(tree : Tree) : Boolean = {
    print(tree) != Cons(IntLit(false), Cons(Plus(), Cons(IntLit(true), Nil())))
  } ensuring(res => res)
}
