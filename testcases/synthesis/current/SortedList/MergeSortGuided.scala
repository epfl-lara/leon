import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object SortedListUnion {
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

  def split(in: List): (List, List) = {
    in match {
      case Cons(h1, Cons(h2, t)) =>
        val r = split(t)
        (Cons(h1, r._1), Cons(h2, r._2))
      case Cons(h1, Nil) =>
        (in, Nil)
      case Nil =>
        (Nil, Nil)
    }
  }

  def merge(in1: List, in2: List): List = {
    require(isSorted(in1) && isSorted(in2))
    (in1, in2) match {
      case (Cons(h1, t1), Cons(h2, t2)) =>
        if (h1 < h2) {
          Cons(h1, merge(t1, in2))
        } else {
          Cons(h2, merge(in1, t2))
        }
      case (l, Nil) => l
      case (Nil, l) => l
    }
  } ensuring {
    (out : List) =>
     (content(out) == content(in1) ++ content(in2)) && isSorted(out)
  }

  def sort(in: List): List = {
    in match {
      case Cons(h1, Cons(h2, t)) =>
        val s = split(in)
        merge(sort(s._1), sort(s._2))
      case _ =>
        ???[List]
    }
  } ensuring {
    (out : List) =>
     content(out) == content(in) && isSorted(out)
  }
}
