import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object SortedList {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

  // proved with unrolling=0
  def size(l: List) : BigInt = (l match {
    case Nil() => BigInt(0)
    case Cons(_, t) => BigInt(1) + size(t)
  }) ensuring(res => res >= BigInt(0))

  //def sizeSynth(l: List): BigInt = choose{ (i: BigInt) => i >= 0 && sizeSynth(Cons(0, l)) == i + 1}
/*
  def content(l: List): Set[BigInt] = l match {
    case Nil() => Set()
    case Cons(i, t) => Set(i) ++ content(t)
  }

  def groundSynth() = Cons(0, Cons(1, Cons(2, Cons(3, Cons(4, Nil()))))) ensuring {
    (out: List) => size(out) == 5
  }

  def insertSynth(in: List, v: BigInt) = Cons(v, in) ensuring {
    (out: List) => content(out) == content(in) ++ Set(v)
  }

  def tailSynth(in: List) = { 
    require(in != Nil())
    in match {
      case Cons(_, tl) => tl
    }
  } ensuring {
    out: List => size(out)+1 == size(in)
  }
*/
  def listOfSizeSynth(i: BigInt) = {
    require(i >= 0)
    choose { out: List => size(out) == i }
  }


}
