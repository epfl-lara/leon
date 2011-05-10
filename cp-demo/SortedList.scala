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

    def isSorted(l: List) : Boolean = l match {
      case Nil() => true
      case Cons(x, Nil()) => true
      case Cons(x, Cons(y, ys)) => x <= y && isSorted(Cons(y, ys))
    }
    // def isSorted(l : List) : Boolean = l match {
    //   case Nil() => true
    //   case Cons(x, xs) => xs match {
    //     case Nil() => true
    //     case Cons(y, _) => x <= y && isSorted(xs)
    //   }
    // }

    def valuesWithin(l: List, lower: Int, upper: Int) : Boolean = l match {
      case Nil() => true
      case Cons(x, xs) => x >= lower && x <= upper && valuesWithin(xs, lower, upper)
    }
}

object SortedList {
  import Lists._

  def main(args : Array[String]) : Unit = {
    val len = if (args.isEmpty) 3 else args(0).toInt
    val set = scala.collection.mutable.Set[List]()

    val c1 : Constraint1[List] = (l : List) => isSorted(l)
    val c2 : Constraint1[List] = (l : List) => valuesWithin(l, 0, len)
    val c3 : Constraint1[List] = (l : List) => size(l) == len

    val combined = c1 && c2 && c3

    // for (list <- ((l : List) => isSorted(l) && valuesWithin(l, 0, len) && size(l) == len).findAll)
    for (list <- combined.findAll)
      set += list
      
    println("size : " + set.size)
    purescala.Stopwatch.printSummary
  }
}
