import scala.collection.immutable.Set

object Giuliano {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def form1(x: Cons, y: Set[Int]) : Boolean = {
    y.contains(x.head) && y.size == x.head
  } ensuring(_ == true)

}

// vim: set ts=4 sw=4 et:
