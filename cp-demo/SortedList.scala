import cp.Definitions._

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

    for (list <- findAll((l : List) => isSorted(l) && valuesWithin(l, 0, len) && size(l) == len))
      set += list
      
    println("size : " + set.size)
    purescala.Stopwatch.printSummary
  }
}
