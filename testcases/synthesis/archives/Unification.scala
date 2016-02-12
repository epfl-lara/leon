import leon.lang._
import leon.lang.synthesis._

object UnificationSynthesis {

  def u1(a1: Int): Int = choose { (x1: Int) => Cons(x1, Nil()) == Cons(a1, Nil()) }

  def u2(a1: Int): Int = choose { (x1: Int) => Cons(x1, Nil()) == Cons(x1, Cons(2, Nil())) }

  def u3(a1: Int): (Int,Int) = choose { (x1: Int, x2: Int) => Cons(x1, Nil()) == Cons(x2, Cons(a1, Nil())) }

  def u4(a1: Int): List = choose { (xs: List) => Cons(a1, xs) == xs }

  def u5(a1: Int): List = choose { (xs: List) => Cons(a1, Nil()) == xs }

  def u6(a1: List): Int = choose { (xs: Int) => Cons(xs, Nil()) == a1 }

  sealed abstract class List
  case class Nil() extends List
  case class Cons(head : Int, tail : List) extends List

  def size(lst : List) : Int = (lst match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)
}
