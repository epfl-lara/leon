import leon.Annotations._
import leon.Utils._

object Union {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case object Nil extends List

  def size(l: List) : Int = (l match {
      case Nil => 0
      case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List): Set[Int] = l match {
    case Nil => Set.empty[Int]
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def insert(in1: List, v: Int): List = {
    Cons(v, in1)
  } ensuring { content(_) == content(in1) ++ Set(v) }

  def delete(in1: List, v: Int): List = {
    in1 match {
      case Cons(h,t) =>
        if (h == v) {
          delete(t, v)
        } else {
          Cons(h, delete(t, v))
        }
      case Nil =>
        Nil
    }
  } ensuring { content(_) == content(in1) -- Set(v) }

  // def union(in1: List, in2: List): List = {
  //   in1 match {
  //     case Cons(h, t) =>
  //       Cons(h, union(t, in2))
  //     case Nil =>
  //       in2
  //   }
  // } ensuring { content(_) == content(in1) ++ content(in2) }

  def union(in1: List, in2: List) = choose {
    (out : List) =>
      content(out) == content(in1) ++ content(in2)
  }
}
