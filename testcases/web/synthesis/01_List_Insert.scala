import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object Insert {
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

  def insert(in1: List, v: BigInt) = {
    choose { (out : List) =>
      content(out) == content(in1) ++ Set(v)
    }
  }
}
