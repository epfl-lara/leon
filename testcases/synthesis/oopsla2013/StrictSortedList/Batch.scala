import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object StrictSortedList {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case object Nil extends List

  def size(l: List) : Int = (l match {
      case Nil => 0
      case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List): Set[Int] = l match {
    case Nil => Set.empty[Int]
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def isSorted(list : List) : Boolean = list match {
    case Nil => true
    case Cons(_, Nil) => true
    case Cons(x1, Cons(x2, _)) if(x1 >= x2) => false
    case Cons(_, xs) => isSorted(xs)
  }

  def insert(in1: List, v: Int) = choose {
    (out : List) =>
      isSorted(in1) && (content(out) == content(in1) ++ Set(v)) && isSorted(out)
  }

  def delete(in1: List, v: Int) = choose {
    (out : List) =>
      isSorted(in1) && (content(out) == content(in1) -- Set(v)) && isSorted(out)
  }

  def union(in1: List, in2: List) = choose {
    (out : List) =>
      isSorted(in1) && isSorted(in2) && (content(out) == content(in1) ++ content(in2)) && isSorted(out)
  }

  def diff(in1: List, in2: List) = choose {
    (out : List) =>
      isSorted(in1) && isSorted(in2) && (content(out) == content(in1) -- content(in2)) && isSorted(out)
  }

}
