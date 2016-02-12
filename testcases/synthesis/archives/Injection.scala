import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object Injection {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  // proved with unrolling=0
  def size(l: List) : Int = (l match {
      case Nil() => 0
      case Cons(_, t) => 1 + size(t)
  }) ensuring(res => res >= 0)


  def listOfSizeSynth(in: List, i: Int) = choose{out: List => (size(out) == i) && (size(in) == i) }
  def listOfSizeSynth2(i: Int) = choose{out: List => size(out) == i }

  def subProblem(in: List, i: Int) = choose{out: List => (size(out) == i) && (size(in)+1 == i) }
  def simple(in: List) = choose{out: List => size(out) == size(in) }

  def invalidInjection(in: List, i: Int) = choose{out: List => (size(out) == i) && (size(in) == i) && in != out }
}
