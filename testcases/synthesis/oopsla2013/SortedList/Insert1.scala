import leon.Annotations._
import leon.Utils._

object Complete {
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

  def isSorted(list : List) : Boolean = list match {
    case Nil => true
    case Cons(_, Nil) => true
    case Cons(x1, Cons(x2, _)) if(x1 > x2) => false
    case Cons(_, xs) => isSorted(xs)
  }

  // def insert1(in1: List, v: Int): List = {
  //   require(isSorted(in1))
  //   in1 match {
  //     case Cons(h, t) =>
  //       if (v < h) {
  //         Cons(v, in1)
  //       } else if (v == h) {
  //         in1
  //       } else {
  //         Cons(h, insert1(t, v))
  //       }
  //     case Nil =>
  //       Cons(v, Nil)
  //   }
  // } ensuring { res => (content(res) == content(in1) ++ Set(v)) && isSorted(res) }

  def insert1(in1: List, v: Int) = choose {
    (out : List) =>
      isSorted(in1) && (content(out) == content(in1) ++ Set(v)) && isSorted(out)
  }

}
