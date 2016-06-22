import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object StrictSortedListDelete {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case object Nil extends List

  def size(l: List): BigInt = (l match {
    case Nil => BigInt(0)
    case Cons(_, t) => BigInt(1) + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List): Set[BigInt] = l match {
    case Nil => Set.empty[BigInt]
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def isSorted(list: List): Boolean = list match {
    case Nil => true
    case Cons(_, Nil) => true
    case Cons(x1, Cons(x2, _)) if(x1 >= x2) => false
    case Cons(_, xs) => isSorted(xs)
  }

  def delete(in: List, v: BigInt) = {
    require(isSorted(in))

    choose( (res : List) =>
        (content(res) == content(in) -- Set(v)) && isSorted(res)
    )
  }
}
