package withOrb

import leon._
import mem._
import higherorder._
import lang._
import annotation._
import collection._
import instrumentation._
import math._
import invariant._

object RunningExample2 {
  sealed abstract class Stream

  private case class SCons(x: BigInt, tfun: () => Stream) extends Stream {
    lazy val tail = tfun()    
  }
  private case class SNil() extends Stream

  def concUntil(l: Stream, i: BigInt): Boolean = {
    l match {
      case c @ SCons(_, _) if i > 0=>
        c.tail.cached && concUntil(l, i - 1)
      case _ => true
    }
  }
  
  def takeLazy[T](n: BigInt, l: Stream): Stream = {
    require(concUntil(l, n))
    l match {
      case c @ SCons(x, _) =>
        if (n == 1)
          SCons(x, lift(SNil()))
        else {
          val newn = n - 1
          val t = c.tail
          SCons(x, () => takeLazy(newn, t))
        }
    }
  } ensuring (res => time <= ?)
}
