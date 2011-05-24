import funcheck.Annotations._
import funcheck.Utils._
import cp.Definitions._
import cp.Terms._

@spec object Specs {
  abstract class List
  case class Cons(head : Int, tail : List) extends List
  case class Nil() extends List

  def concat(l1 : List, l2 : List) : List = (l1 match {
    case Nil() => l2
    case Cons(x,xs) => Cons(x, concat(xs, l2))
  })

  def isSorted(l : List) : Boolean = l match {
    case Nil() => true
    case Cons(_, Nil()) => true
    case Cons(x, Cons(y, xs)) => x <= y && isSorted(Cons(y, xs))
  }

  def content(l : List) : Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ content(xs)
  }

  def size(l : List) : Int = (l match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring (_ >= 0)

  def occurrences(l : List, i : Int) : Int = (l match {
    case Nil() => 0
    case Cons(x, xs) => (if (x == i) 1 else 0) + occurrences(xs, i)
  }) ensuring (_ >= 0)

  def isPermutedSublistOf(l1 : List, l2 : List) : Boolean = l1 match {
    case Nil() => true
    case Cons(x, xs) => occurrences(l1, x) <= occurrences(l2, x) && isPermutedSublistOf(xs, l2)
  }

  def isPermutationOf(l1 : List, l2 : List) : Boolean =
    isPermutedSublistOf(l1, l2) && isPermutedSublistOf(l2, l1)
}

object ListMethods {
  import Specs._

  def last(list : List) : Int = {
    val (elem, _) = ((e : Int, zs : List) => concat(zs, Cons(e, Nil())) == list).solve
    elem
  }

  def add(list : List, elem : Int) : List =
    ((l : List) => content(l) == content(list) ++ Set(elem)).solve

  def sort(list : List) : List =
    ((l : List) => isPermutationOf(l, list) && isSorted(l)).solve

  def main(args: Array[String]) : Unit = {
    val len = if (args.isEmpty) 5 else args(0).toInt
    val l = ((l : List) => size(l) == len).solve

    println("Here is a list: " + l)
    println("Here is its last element: " + last(l))

    val added = add(l, 42)
    println("Here is that list with 42 added to it: " + added)

    val sorted = sort(added)
    println("Here is the previous list, this time sorted: " + sorted)
  }
}
