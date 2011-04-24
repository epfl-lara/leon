import cp.Definitions._
import cp.Utils.Timer

object Lists {
    @spec sealed abstract class List
    @spec case class Cons(head: Int, tail: List) extends List
    @spec case class Nil() extends List

    @spec def size(l: List) : Int = (l match {
        case Nil() => 0
        case Cons(_, t) => 1 + size(t)
    }) ensuring(res => res >= 0)

    @spec def isSorted(l: List) : Boolean = l match {
      case Nil() => true
      case Cons(x, Nil()) => true
      case Cons(x, Cons(y, ys)) => x <= y && isSorted(Cons(y, ys))
    }

    @spec def valuesWithin(l: List, lower: Int, upper: Int) : Boolean = l match {
      case Nil() => true
      case Cons(x, xs) => x >= lower && x <= upper && valuesWithin(xs, lower, upper)
    }
}

object SortedList {
  import Lists._

  def main(args : Array[String]) : Unit = {
    val len = if (args.isEmpty) 3 else args(0).toInt
    val set = scala.collection.mutable.Set[List]()

    val timer = new Timer("Sorted list enumeration", true)
    timer.start
    for (list <- findAll((l : List) => isSorted(l) && valuesWithin(l, 0, len) && size(l) == len))
      set += list
    timer.stop
      
    println("size : " + set.size)
  }
}
