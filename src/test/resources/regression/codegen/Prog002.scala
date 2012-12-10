object Prog002 {
  sealed abstract class List
  case class Nil() extends List
  case class Cons(head : Int, tail : List) extends List

  def isNil(l : List) : Boolean = {
    l == Nil()
  }

  def size(l : List) : Int = l match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }
}
