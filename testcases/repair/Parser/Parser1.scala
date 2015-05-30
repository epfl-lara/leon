import leon._
import leon.lang._
import leon.collection._

object Parser {
  abstract class Token
  case object LParen extends Token
  case object RParen extends Token
  case class Id(id : Int) extends Token
  
  abstract class Tree
  case class App(args : List[Tree]) extends Tree
  case class Leaf(id : Int) extends Tree

  def parse(in : List[Token]) : (Option[Tree], List[Token]) = { in match {
    case Cons(Id(s), tl) => 
      (Some[Tree](Leaf(s)),tl)
    case Cons(LParen, tl) => parseMany(tl) match {
      case (Some(trees:Cons[Tree]), Cons(RParen,rest)) => 
        (Some[Tree](App(trees)), rest)
      case (_, rest) => (None[Tree](), rest)
    }
    case _ => (None[Tree](), in)
  }} ensuring { _ match {
    case ( Some(tree), rest@Cons(h,_)) => 
      print(tree, rest) == in
    case ( None(), Cons(h,_) ) => 
      h == RParen
    case _ => true
  }}

  def parseMany(in : List[Token]) : (Option[List[Tree]], List[Token]) = { parse(in) match {
    case (None(), rest) /*if rest == in*/ => (Some[List[Tree]](Nil()), in) // FIXME: forgot condition
    //case (None(), rest) => (None[List[Tree]](), rest)
    case (Some(tree), rest) => parseMany(rest) match {
      case ( None(), rest2) => (None[List[Tree]](), rest2)
      case ( Some(trees), rest2) =>
        ( Some[List[Tree]](tree::trees), rest2 )
    }
  }} ensuring { _ match {
    case ( Some(t), rest@Cons(h, _) ) => 
      h == RParen && printL(t, rest) == in 
    case ( None(), Cons(h, _)) => 
      h == RParen
    case _ => true
  }}


  def printL(args : List[Tree], rest : List[Token]) : List[Token] = args match {
    case Nil() => rest
    case Cons(h,t) => print(h, printL(t, rest))
  }
  
  def print(t : Tree, rest : List[Token]) : List[Token] = t match {
    case Leaf(s) => Id(s) :: rest
    case App(args) => LParen :: printL(args, RParen :: rest) 
  }

}
