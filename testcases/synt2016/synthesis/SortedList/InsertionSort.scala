import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object SortedListInsertionSort {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case object Nil extends List

  def size(l: List): BigInt = (l match {
    case Nil => BigInt(0)
    case Cons(_, t) => BigInt(1) + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List): Set[BigInt] = l match {
    case Nil => Set.empty[BigInt]
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def isSorted(list: List): Boolean = list match {
    case Nil => true
    case Cons(_, Nil) => true
    case Cons(x1, Cons(x2, _)) if(x1 > x2) => false
    case Cons(_, xs) => isSorted(xs)
  }

  def insert(in1: List, v: BigInt): List = {
    require(isSorted(in1))
    in1 match {
      case Cons(h, t) =>
        if (v < h) {
          Cons(v, in1)
        } else if (v == h) {
          in1
        } else {
          Cons(h, insert(t, v))
        }
      case Nil =>
        Cons(v, Nil)
    }

  } ensuring { res => (content(res) == content(in1) ++ Set(v)) && isSorted(res) }

  def insertionSort(in1: List): List = {
    choose { (out: List) =>
      content(out) == content(in1) && isSorted(out)
    }
  }
}
