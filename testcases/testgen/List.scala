import leon.lang._
import leon.annotation._

object List {

  abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  @main
  def size(l: List): Int = (l match {
    case Cons(_, tail) => sizeTail(tail, 1)
    case Nil() => 0
  }) ensuring(_ >= 0)

  def sizeTail(l2: List, acc: Int): Int = l2 match {
    case Cons(_, tail) => sizeTail(tail, acc+1)
    case Nil() => acc
  }
}
