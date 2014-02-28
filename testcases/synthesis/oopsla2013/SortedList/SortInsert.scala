import leon.annotation._
import leon.lang._

object Complete {
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
    case Cons(x1, Cons(x2, _)) if(x1 > x2) => false
    case Cons(_, xs) => isSorted(xs)
  }

  def insert(in1: List, v: Int): List = {
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


  def delete(in1: List, v: Int): List = {
    require(isSorted(in1))
    in1 match {
      case Cons(h,t) =>
        if (h < v) {
          Cons(h, delete(t, v))
        } else if (h == v) {
          delete(t, v)
        } else {
          in1
        }
      case Nil =>
        Nil
    }
  } ensuring { res => content(res) == content(in1) -- Set(v) && isSorted(res) }

  def union(in1: List, in2: List): List = {
    require(isSorted(in1) && isSorted(in2))
    in1 match {
      case Cons(h1, t1) =>
        insert(union(t1, in2), h1)
      case Nil =>
        in2
    }
  } ensuring { res => content(res) == content(in1) ++ content(in2) && isSorted(res) }

  def diff(in1: List, in2: List): List = {
    require(isSorted(in1) && isSorted(in2))
    in2 match {
      case Cons(h2, t2) =>
        diff(delete(in1, h2), t2)
      case Nil =>
        in1
    }
  } ensuring { res => content(res) == content(in1) -- content(in2) && isSorted(res) }

  // ***********************
  // Sorting algorithms
  // ***********************
  def sortSpec(in : List, out : List) : Boolean = {
    content(out) == content(in) && isSorted(out)
  }

  // def sort1(in : List) : List = (in match {
  //   case Nil => Nil
  //   case Cons(x, xs) => insert(sort1(xs), x)
  // }) ensuring(res => sortSpec(in, res))

  // // Not really quicksort, neither mergesort.
  // def sort2(in : List) : List = (in match {
  //   case Nil => Nil
  //   case Cons(x, Nil) => Cons(x, Nil)
  //   case _ =>
  //     val (s1,s2) = split(in)
  //     union(sort2(s1), sort2(s2))
  // }) ensuring(res => sortSpec(in, res))

  def sort(list: List): List = choose {
    (res: List) => sortSpec(list, res)
  }

}
