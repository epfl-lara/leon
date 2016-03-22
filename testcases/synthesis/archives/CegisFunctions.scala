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

  def insert(l: List, i: Int) = {
    Cons(i, l)
  }.ensuring(res => size(res) == size(l)+1 && content(res) == content(l) ++ Set(i))

  def testInsert(l: List, i: Int) = {
    choose { (o: List) => size(o) == size(l) + 1 }
  }

  def testDelete(l: List, i: Int) = {
    choose { (o: List) => size(o) == size(l) - 1 }
  }
}
