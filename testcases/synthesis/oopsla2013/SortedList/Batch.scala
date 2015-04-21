import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object SortedList {
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

  def insert(in1: List, v: Int) = {
    require(isSorted(in1))

    choose {
      (out : List) =>
        (content(out) == content(in1) ++ Set(v)) && isSorted(out)
    }
  }

  def delete(in1: List, v: Int) = {
    require(isSorted(in1))

    choose {
      (out : List) =>
        isSorted(in1) && (content(out) == content(in1) -- Set(v)) && isSorted(out)
    }
  }

  def union(in1: List, in2: List) = {
    require(isSorted(in1) && isSorted(in2))

    choose {
      (out : List) =>
        (content(out) == content(in1) ++ content(in2)) && isSorted(out)
    }
  }

  def diff(in1: List, in2: List) = {
   require(isSorted(in1) && isSorted(in2))

    choose {
      (out : List) =>
        (content(out) == content(in1) -- content(in2)) && isSorted(out)
    }
  }

  // ***********************
  // Sorting algorithms
  // ***********************

  def splitSpec(list : List, res : (List,List)) : Boolean = {
    val s1 = size(res._1)
    val s2 = size(res._2)
    abs(s1 - s2) <= 1 && s1 + s2 == size(list) &&
    content(res._1) ++ content(res._2) == content(list) 
  }

  def abs(i : Int) : Int = {
    if(i < 0) -i else i
  } ensuring(_ >= 0)

  def sortSpec(in : List, out : List) : Boolean = {
    content(out) == content(in) && isSorted(out)
  }

  def split(list : List) : (List,List) = {
    choose { (res : (List,List)) => splitSpec(list, res) }
  }

  def sort(list: List): List = choose {
    (res: List) => sortSpec(list, res)
  }

}
