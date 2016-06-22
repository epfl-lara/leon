import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object ListOfSize {
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

  def listOfSize(s: BigInt) = {
    require(s >= 0)
    choose((l: List) => size(l) == s)
  }
}
