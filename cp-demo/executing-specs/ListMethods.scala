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

  def valuesWithin(l : List, lower : Int, upper : Int) : Boolean = l match {
    case Nil() => true
    case Cons(x, xs) => x >= lower && x <= upper && valuesWithin(xs, lower, upper)
  }

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
    val bound = if (args.isEmpty) 5 else args(0).toInt
    val nbLists = if (args.size == 2) args(1).toInt else 5

    // val l = ((l : List) => size(l) == bound).solve
    // val lists = for (i <- 1 to nbLists) yield ((l : List) => size(l) == bound).solve
    // val lists = ((l : List) => size(l) == bound && valuesWithin(l, 0, bound - 1)).findAll.toList
    val lists = Seq(
      Cons(1, Cons(2, Cons(3, Nil()))),
      Cons(2, Cons(1, Cons(3, Nil()))),
      Cons(1, Cons(2, Cons(4, Nil()))),
      Cons(5, Cons(2, Cons(3, Nil()))),
      Cons(7, Cons(2, Cons(9, Nil()))))

    println("Here are lists:")
    println(lists.mkString("\n"))

    // println("Here is its last element: " + last(l))

    val added = lists.map(add(_, 42))
    println("Here are those lists with 42 added to them:")
    println(added.mkString("\n"))

    // val sorted = sort(added)
    // println("Here is the previous list, this time sorted: " + sorted)
  }
}
