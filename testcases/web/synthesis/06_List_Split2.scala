import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object List {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case object Nil extends List

  def size(l: List) : BigInt = (l match {
    case Nil => BigInt(0)
    case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List): Set[BigInt] = l match {
    case Nil => Set.empty[BigInt]
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def abs(i: BigInt) : BigInt = {
    if(i < 0) -i else i
  } ensuring(_ >= 0)

  def split(list: List): (List, List) = {
    choose { (res : (List, List)) =>
      (content(res._1) ++ content(res._2) == content(list)) &&
      (abs(size(res._1) - size(res._2)) <= 1)
    }
  }

}
