import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object List {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def inv(l: List): Boolean = true

  def size(l: List) : Int = (l match {
      case Nil() => 0
      case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def content(l: List): Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(i, t) => Set(i) ++ content(t)
  }


  // To Synthesize:


  def insert(in: List, v: Int) = choose {
    (out: List) => inv(in) && (content(out) == (content(in) ++ Set(v))) && inv(out)
  }

  def delete(in: List, v: Int) = choose {
    (out: List) => inv(in) && (content(out) == (content(in) -- Set(v))) && inv(out)
  }

  def union(in1: List, in2: List) = choose {
    (out: List) => inv(in1) && inv(in2) && (content(out) == (content(in1) ++ content(in2))) && inv(out)
  }

  def intersection(in1: List, in2: List) = choose {
    (out: List) => inv(in1) && inv(in2) && (content(out) == (content(in1) & content(in2))) && inv(out)
  }
}
