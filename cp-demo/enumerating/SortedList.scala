import cp.Definitions._
import cp.Terms._

@spec object Lists {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def size(l: List) : Int = (l match {
      case Nil() => 0
      case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List): Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ content(xs)
  }
  def isSorted(l : List) : Boolean = l match {
    case Nil() => true
    case Cons(x, xs) => xs match {
      case Nil() => true
      case Cons(y, _) => x <= y && isSorted(xs)
    }
  }

  def listEq(l1: List, l2: List): Boolean = l1 == l2

  def valuesWithin(l: List, lower: Int, upper: Int) : Boolean = l match {
    case Nil() => true
    case Cons(x, xs) => x >= lower && x <= upper && valuesWithin(xs, lower, upper)
  }

  def isAppend(head1: List, tail1: List, head2: List, tail2: List, head3 : List, tail3 : List): Boolean = {
    head3 == head1 && tail3 == tail2 && tail1 == head2
  }
}

object SortedList {
  import Lists._

  def anyList = ((l: List) => true).lazyFindAll
  def hasSize(i: Int) = ((l: List) => size(l) == i).lazyFindAll

  def main(args : Array[String]) : Unit = {
    val len = if (args.isEmpty) 3 else args(0).toInt

    f1(len)
    // f2(len)
    // f3(len)
    // f4()
  }

  def f1(len: Int) {
    val set = scala.collection.mutable.Set[List]()

    for (list <- ((l : List) => isSorted(l) && valuesWithin(l, 0, len) && size(l) == len).findAll)
      set += list
      
    println("size : " + set.size)
    purescala.Stopwatch.printSummary
  }

  def f2(len: Int) {
    for {
      l1 <- hasSize(len)
      l2 <- hasSize(len)
      if isSorted(l1) && isSorted(l2) && content(l1) == content(l2) && !listEq(l1, l2)
    } {
      println(l1.force(), l2.force())
    }
  }

  def f3(len: Int) {
    for ((l1, l2) <- ((l1:List, l2: List) => size(l1) == len && size(l2) == len && isSorted(l1) && isSorted(l2) && content(l1) == content(l2) && !listEq(l1, l2)).findAll)
      println(l1, l2)
  }

  def f4() {
    println(((l1: List, l2: List, h1: List, h2: List) =>  
      l1 == Cons(1, Cons(2, Cons(3, h1))) &&
      l2 == Cons(4, Cons(5, Cons(6, h2))) &&
      h1 == l2).solve)
  }

  def f5() {
    
  }
}
