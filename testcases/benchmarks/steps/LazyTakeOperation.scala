package takelazy

import leon._
import mem._
import higherorder._
import lang._
import annotation._
import collection._
import instrumentation._
import math._
import invariant._

/**
* This the small running example shown in Fig. 7. This is not evaluted
* in experiments as it is subsumed by several other complex benchmarks.
* For instance, one of the functions in the `Dequeue` benchamrk has this function.
**/
object RunningExample2 {
  sealed abstract class Stream

  private case class SCons(x: BigInt, tfun: () => Stream) extends Stream {
    lazy val tail = tfun()
  }
  private case class SNil() extends Stream

  def concUntil(l: Stream, i: BigInt): Boolean = {
    l match {
      case c @ SCons(_, _) =>
        if (i > 0){
          cached(c.tail) && concUntil(c.tail, i - 1) 
        } else true
      case _ => true
    }
  }

  def takeLazy[T](n: BigInt, l: Stream): Stream = {
    require(concUntil(l, n))
    l match {
      case c @ SCons(x, _) =>
        if (n > 0) {
          val newn = n - 1
          val t = c.tail
          SCons(x, () => takeLazy(newn, t))
        } else SNil()
      case _ => SNil()
    }
  } ensuring (res => steps <= ?)
}
