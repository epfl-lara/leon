import scala.collection.immutable.Set

object InsertionSort {
  sealed abstract class List
  case class Cons(head:Int,tail:List) extends List
  case class Nil() extends List

  def contents(l: List): Set[Int] = l match {
    case Nil() => Set.empty
    case Cons(x,xs) => contents(xs) ++ Set(x)
  }

  def isSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, xs) => xs match {
      case Nil() => true
      case Cons(y, ys) => x < y && isSorted(Cons(y, xs))
    }
  }    

  def sortedIns(e: Int, l: List): List = (l match {
    case Nil() => Cons(e,Nil())
    case Cons(x,xs) => if (x < e) Cons(x,sortedIns(e, xs))  else Cons(e, l)
  }) ensuring(res => contents(res) == contents(l) ++ Set(e))

  def sorted(l: List): List = (l match {
    case Nil() => Nil()
    case Cons(x,xs) => sortedIns(x, sorted(xs))
  }) ensuring(res => contents(res) == contents(l))// && isSorted(res))

  def main(args: Array[String]): Unit = {
    val ls: List = Cons(5, Cons(2, Cons(4, Cons(5, Cons(1, Cons(8,Nil()))))))

    println(ls)
    println(sorted(ls))
  }
}
