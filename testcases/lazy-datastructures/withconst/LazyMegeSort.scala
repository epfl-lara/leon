package lazybenchmarks

import leon.lazyeval._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
//import leon.invariant._

object MergeSort {

  // TODO: making this parametric will break many things. Fix them
  sealed abstract class LList {
    def size: BigInt = {
      this match {
        case SNil()      => BigInt(0)
        case SCons(x, t) => 1 + ssize(t)
      }
    } ensuring (_ >= 0)
  }
  case class SCons(x: BigInt, tail: $[LList]) extends LList
  case class SNil() extends LList
  def ssize(l: $[LList]): BigInt = (l*).size

  sealed abstract class List {
    def size: BigInt = {
      this match {
        case Cons(_, xs) => 1 + xs.size
        case _           => BigInt(0)
      }
    } ensuring (_ >= 0)
  }
  case class Cons(x: BigInt, tail: List) extends List
  case class Nil() extends List

  def length(l: List): BigInt = {
    l match {
      case Nil()       => BigInt(0)
      case Cons(x, xs) => 1 + length(xs)
    }
  } ensuring (res => res >= 0 && res == l.size && stack <= 14 * l.size + 15)

  def split(l: List, n: BigInt): (List, List) = {
    require(n > 0 && n < l.size)
    l match {
      case Nil() => (Nil(), l)
      case Cons(x, xs) =>
        if (n == 1) {
          (Cons(x, Nil()), xs)
        } else {
          val (fst, snd) = split(xs, n - 1)
          (Cons(x, fst), snd)
        }
    }
  } ensuring (res => res._2.size == l.size - n && res._1.size == n && stack <= 25 * l.size - 1)

  /*
   * Proving standalone bound for merge requires preconditions.
   */
  def merge(a: $[LList], b: $[LList]): LList = (b.value match {
    case SNil() => a.value
    case bl @ SCons(x, xs) =>
      a.value match {
        case SNil() => bl
        case SCons(y, ys) =>
          if (y < x)
            SCons(y, $(merge(ys, b)))
          else
            SCons(x, $(merge(a, xs)))
      }
  }) //ensuring (res => ssize(a) + ssize(b) == res.size)

  /**
   * Note the time is not O(n) but only O(n log n) since
   * we have time recurrence T(n) = 2T(n/2) + O(n)
   */
  def mergeSort(l: List): LList = (l match {
    case Nil()          => SNil()
    case Cons(x, Nil()) => SCons(x, $(SNil()))
    case _ =>
      val (fst, snd) = split(l, length(l) / 2)
      merge($(mergeSort(fst)), $(mergeSort(snd)))

  }) ensuring (res => stack <= 81 * l.size + 35) // res.size == l.size
}
