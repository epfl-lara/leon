import leon.Annotations._
import leon.Utils._

object Insert {
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

  //def insert(in1: List, v: Int): List = {
  //  Cons(v, in1)
  //} ensuring { content(_) == content(in1) ++ Set(v) }

  def insert(in1: List, v: Int) = choose {
    (out : List) =>
      content(out) == content(in1) ++ Set(v)
  }
}
