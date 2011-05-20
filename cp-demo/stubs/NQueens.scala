import cp.Definitions._

object NQueens {
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

  @spec def allDistinct(l : List) : Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, Cons(y, ys)) => x != y && allDistinct(Cons(x, ys)) && allDistinct(Cons(y, ys))
  }

  def hasSize(sz : Int) : Constraint1[List] =
    if(sz <= 0) {
      (l : List) => l == Nil()
    } else {
      (l : List) => l match {
        case Cons(_, xs) => hasSize(sz - 1)



  def main(args : Array[String]) : Unit = {
    val len = if (args.isEmpty) 4 else args(0).toInt
    val set = scala.collection.mutable.Set[List]()

    for (list <- findAll((l : List) => allDistinct(l) && valuesWithin(l, 0, len-1) && size(l) == len))
      set += list
      
    // println(set.mkString("\n"))
    println("size : " + set.size)
  }
}
