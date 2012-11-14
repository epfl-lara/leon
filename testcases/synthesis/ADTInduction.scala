import scala.collection.immutable.Set
import leon.Annotations._
import leon.Utils._

object SortedList {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  // proved with unrolling=0
  def size(l: List) : Int = (l match {
      case Nil() => 0
      case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  //def sizeSynth(l: List): Int = choose{ (i: Int) => i >= 0 && sizeSynth(Cons(0, l)) == i + 1}

  def content(l: List): Set[Int] = l match {
    case Nil() => Set()
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def deleteSynth(in: List, v: Int) = choose{ (out: List) => !(content(out) contains v) && size(out)+1 >= size(in) }

  def isSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, Cons(y, ys)) => x <= y && isSorted(Cons(y, ys))
  }
}
