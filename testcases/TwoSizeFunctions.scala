import funcheck.Utils._
import funcheck.Annotations._

object TwoSizeFunctions {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def size1(l: List) : Int = (l match {
    case Cons(_, xs) => size1(xs) + 1
    case Nil() => 0
  }) ensuring(_ >= 0)

  def size2(l: List) : Int = size2acc(l, 0)
  def size2acc(l: List, acc: Int) : Int = {
    require(acc >= 0)
    l match {
      case Nil() => acc
      case Cons(_, xs) => size2acc(xs, acc+1)
    }
  } ensuring(_ >= 0)

  @induct
  def sizesAreEquiv(l: List) : Boolean = {
    require(size1(l) < 25) // remove and it can't find it.
    size1(l) == size2(l)
  } holds
}
