import leon.Utils._

object UnificationSynthesis {

  def u1(a1: Int): Int = choose { (x1: Int) => Cons(x1, Nil()) == Cons(a1, Nil()) }
  def u2(a1: Int): Int = choose { (x1: Int) => Cons(x1, Nil()) == Cons(x1, Cons(2, Nil())) }
  def u3(a1: Int): List = choose { (xs: List) => Cons(a1, xs) == xs }

  sealed abstract class List
  case class Nil() extends List
  case class Cons(head : Int, tail : List) extends List

  def size(lst : List) : Int = (lst match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)
}
