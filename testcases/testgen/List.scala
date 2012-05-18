import leon.Utils._

object List {

  abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def size(l: List): Int = waypoint(1, (l match {
    case Cons(_, tail) => 1 + size(tail)
    case Nil() => 0
  })) ensuring(_ >= 0)

}
