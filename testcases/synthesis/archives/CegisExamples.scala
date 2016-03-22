import leon.lang._
import leon.lang.synthesis._

object CegisTests {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  // proved with unrolling=0
  def size(l: List) : Int = (l match {
    case Nil() => 0
    case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List): Set[Int] = l match {
    case Nil() => Set()
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def cegis1(a: Int) = choose { x: List => size(x) == 1 && content(x) == Set(a) }
  def cegis2(a: Int) = choose { x: List => size(x) == 2 && content(x) == Set(a) }
  def cegis3(a: Int) = choose { x: List => size(x) == 3 && content(x) == Set(a) }
  def cegis4(a: Int) = choose { x: List => size(x) == 4 && content(x) == Set(a) }
  def cegis5(a: Int) = choose { x: List => size(x) == 5 && content(x) == Set(a) }
}
