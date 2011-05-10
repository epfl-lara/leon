import funcheck.Utils._
import funcheck.Annotations._

object Test {
    sealed abstract class List
    case class Cons(head: Int, tail: List) extends List
    case class Nil() extends List

    @axiomatize
    def size(l: List) : Int = (l match {
        case Nil() => 0
        case Cons(_, t) => 1 + size(t)
    }) ensuring(res => res >= 0)

    @axiomatize
    def isSorted(l : List) : Boolean = l match {
      case Nil() => true
      case Cons(x, xs) => xs match {
        case Nil() => true
        case Cons(y, _) => x <= y && isSorted(xs)
      }
    }

    def valuesWithin(l: List, lower: Int, upper: Int) : Boolean = l match {
      case Nil() => true
      case Cons(x, xs) => x >= lower && x <= upper && valuesWithin(xs, lower, upper)
    }

    def findOne(l : List) : Boolean = {
      isSorted(l) && valuesWithin(l, 0, 3) && size(l) == 3
    } ensuring(res => !res)
}
