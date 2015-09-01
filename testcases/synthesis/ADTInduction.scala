import leon.annotation._
import leon.lang.synthesis._
import leon.lang._

object SortedList {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  // proved with unrolling=0
  def size(l: List) : Int = (l match {
    case Nil() => 0
    case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  //def sizeSynth(l: List): Int = choose{ (i: Int) => i >= 0 && sizeSynth(Cons(0, l)) == i + 1}

  def content(l: List): Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(i, t) => Set(i) ++ content(t)
  }

  //def artifialSubcase(v : Int) = choose {
  //  (out : List) =>
  //    content(out) == (content(Nil()) -- Set(v))
  //}

  def deleteSynth(in: List, v: Int) = (in match {
    case Cons(head22, tail21) =>
      (tail21 match {
        case Cons(head23, tail23) =>
          (choose { (out: List) =>
            (content(out) == (content(Cons(head22, Cons(head23, tail23))) -- Set(v)))
          })
        case _ =>
          (choose { (out: List) =>
            (content(out) == (content(Cons(head22, Nil())) -- Set(v)))
          })
      })
    case _ =>
      Nil()
  })

  def concatSynth(in1: List, in2: List) = choose {
    (out : List) =>
      content(out) == content(in1) ++ content(in2)
  }

  def isSorted(l: List): Boolean = l match {
    case Nil() => true
    case Cons(x, Nil()) => true
    case Cons(x, Cons(y, ys)) => x <= y && isSorted(Cons(y, ys))
  }
}
