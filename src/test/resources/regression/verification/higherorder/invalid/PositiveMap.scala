
import leon.Utils._

object PositiveMap {
  
  abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def positive(list: List): Boolean = list match {
    case Cons(head, tail) => if (head < 0) false else positive(tail)
    case Nil() => true
  }

  def positiveMap_failling_1(f: (Int) => Int, list: List): List = {
    require(forall((a: Int) => f(a) > -2))
    list match {
      case Cons(head, tail) => Cons(f(head), positiveMap_failling_1(f, tail))
      case Nil() => Nil()
    }
  } ensuring { res => positive(res) }
}

// vim: set ts=4 sw=4 et:
