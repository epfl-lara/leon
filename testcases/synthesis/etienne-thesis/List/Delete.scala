import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object Delete {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case object Nil extends List

  def size(l: List) : BigInt = (l match {
    case Nil => BigInt(0)
    case Cons(_, t) => BigInt(1) + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List): Set[BigInt] = l match {
    case Nil => Set.empty[BigInt]
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def insert(in1: List, v: BigInt): List = {
    Cons(v, in1)
  } ensuring { content(_) == content(in1) ++ Set(v) }

  //def delete(in1: List, v: BigInt): List = {
  //  in1 match {
  //    case Cons(h,t) =>
  //      if (h == v) {
  //        delete(t, v)
  //      } else {
  //        Cons(h, delete(t, v))
  //      }
  //    case Nil =>
  //      Nil
  //  }
  //} ensuring { content(_) == content(in1) -- Set(v) }

  def delete(in1: List, v: BigInt) = choose {
    (out : List) =>
      content(out) == content(in1) -- Set(v)
  }
}
