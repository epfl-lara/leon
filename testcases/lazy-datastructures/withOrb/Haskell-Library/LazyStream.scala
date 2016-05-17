package stream

import leon._
import lang._
import annotation._
import instrumentation._
import mem._
import higherorder._
import collection._
import invariant._
import StreamLibrary._

object LazyRepeat {

  /**
   * The function lazyappend appends a list to a stream,
   * returning a stream of all the list elements
   * followed by all the original stream elements.
   */
  def lazyappend(l: List[BigInt], s: LList): LList = {
    l match {
      case Nil()         => s
      case Cons(x, tail) => SCons(x, Susp(() => lazyappend(tail, s)))
    }
  } ensuring (_ => time <= ?) // Orb result: ??

  /**
   * The function repeat expects a list and returns a
   * stream that represents infinite appends of the
   * list to itself.
   */
  def repeat(l: List[BigInt]): LList = {
    l match {
      case Nil() => SNil()
      case Cons(x, t) =>
        SCons(x, Susp(() => lazyappend(t, repeat(l))))
    }
  } ensuring (_ => time <= ?) // Orb result: ??

  def nthElemInRepeat(n: BigInt, l: List[BigInt]) = {
    require(n >= 0)
    getnthElem(n, repeat(l))
  } ensuring (_ => time <= ? * n + ?) // Orb result: ??
}
