import leon.lang._
import leon.lang.synthesis._

object FilterNonNeg {

  abstract class List
  case object Nil extends List
  case class Cons(h: Int, t: List) extends List

  def filter(l: List, f: Int => Boolean): List = {
    l match {
      case Cons(h, t) => if (f(h)) Cons(h, filter(t, f)) else filter(t, f)
      case Nil => Nil
    }
  }

  def test(in: List): List = {
    ???[List]
  } ensuring {
    out => (in, out) passes {
      case Cons(1, Cons(2, Cons(3, Cons(4, Nil))))    => Cons(1, Cons(2, Cons(3, Cons(4, Nil))))
      case Cons(-1, Cons(-2, Cons(3, Cons(-4, Nil)))) => Cons(3, Nil)
      case Cons(1, Cons(-2, Cons(3, Cons(-4, Nil))))  => Cons(1, Cons(3, Nil))
    }
  }
}
