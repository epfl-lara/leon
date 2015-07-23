import leon.lang._
import leon.annotation._

object TwoSizeFunctions {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def size1(l: List) : BigInt = (l match {
    case Cons(_, xs) => size1(xs) + 1
    case Nil() => BigInt(0)
  }) ensuring(_ >= 0)

  def size2(l: List) : BigInt = size2acc(l, 0)
  def size2acc(l: List, acc: BigInt) : BigInt = {
    require(acc >= 0)
    l match {
      case Nil() => acc
      case Cons(_, xs) => size2acc(xs, acc+1)
    }
  } ensuring(res => res == size1(l) + acc)

  def sizesAreEquiv(l : List) : Boolean = 
    (size1(l) == size2(l)) holds

/*
  def sizesAreEquiv1(l: List) : Boolean = {
    require(size1(l) < 25) // remove and it can't find it.
    size1(l) == size2(l)
  } holds

  @induct
  def sizesAreEquiv(l: List, k : Int) : Boolean = {
    require (k >= 0)
    size1(l) + k == size2acc(l, k)
  } holds
*/
}
