import funcheck.Utils._

object Test {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def append(value: Int, list: List) : List = list match {
    case Nil() => Cons(value, Nil())
    case Cons(x, xs) => Cons(x, append(value, xs))
  }

  def isSorted(list: List) : Boolean = list match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, c @ Cons(y, ys)) => x <= y && isSorted(c)
  }

  def isSorted2(list: List) : Boolean = list match {
    case Cons(x, c @ Cons(y, ys)) => x <= y && isSorted2(c)
    case _ => true
  }

  def sameSorted(list: List) : Boolean = {
    isSorted(list) == isSorted2(list)
  } holds
}
