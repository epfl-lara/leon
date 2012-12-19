import scala.collection.immutable.Set
import leon.Annotations._
import leon.Utils._

object List {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def size(l: List) : Int = (l match {
      case Nil() => 0
      case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List): Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def isSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, Cons(y, ys)) => x <= y && isSorted(Cons(y, ys))
  }

  def isStrictSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, Cons(y, ys)) => x < y && isSorted(Cons(y, ys))
  }

  def deleteSynth(in: List, v: Int) = choose {
    (out: List) => (content(out) == (content(in) -- Set(v)))
  }

  def deleteSortedSynth(in: List, v: Int) = choose {
    (out: List) => isSorted(in) && (content(out) == (content(in) -- Set(v))) && isSorted(out)
  }

  def insertSynth(in: List, v: Int) = choose {
    (out: List) => (content(out) == (content(in) ++ Set(v)))
  }

  def insertSortedSynth(in: List, v: Int) = choose {
    (out: List) => isSorted(in) && (content(out) == (content(in) ++ Set(v))) && isSorted(out)
  }

  def insertStrictSortedSynth(in: List, v: Int) = choose {
    (out: List) => isStrictSorted(in) && (content(out) == (content(in) ++ Set(v))) && isStrictSorted(out)
  }

  def concatSynth(in1: List, in2: List) = choose {
    (out : List) => content(out) == content(in1) ++ content(in2)
  }

  def mergeSynth(in1: List, in2: List) = choose {
    (out : List) => isSorted(in1) && isSorted(in2) && (content(out) == content(in1) ++ content(in2)) && isSorted(out)
  }

  def mergeStrictSynth(in1: List, in2: List) = choose {
    (out : List) => isStrictSorted(in1) && isStrictSorted(in2) && (content(out) == content(in1) ++ content(in2)) && isStrictSorted(out)
  }

}
