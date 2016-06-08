package withorb

import leon._
import lang._
import annotation._
import instrumentation._
import mem._
import higherorder._
import collection._
import invariant._

/**
 * Hint: requires unrollfactor=4
 */
object ZipWithAndFibStream {
  /**
   *  An infinite integer stream.
   *  Technically, the data structure is *not* infinite but the tail has a higher-order function.
   */
  case class SCons(x: BigInt, tailFun: ValOrSusp) {
    @inline
    def tail = tailFun match {
      case s@Susp(f) => s.fval
      case Val(x) => x
    }
    // this will not modify state
    @inline
    def tailVal = tailFun match {
      case s@Susp(f) => s.fval*
      case Val(x) => x
    }
    @inline
    def tailCached = tailFun match {
      case Val(_) => true
      case s => s.fval.cached
    }
  }

  sealed abstract class ValOrSusp {
    // ideally, fval should not be called on `Val` as it would unnecessarily cache it.
    lazy val fval = {
      this match {
        case Susp(f) => f()
        case Val(x) => x
      }
    }
  }
  private case class Val(x: SCons) extends ValOrSusp
  private case class Susp(fun: () => SCons) extends ValOrSusp

  /**
   * A generic higher-order `zipWithFun` function.
   * The function is private so the targets of `f` are within scope.
   */
  private def zipWithFun(f: (BigInt, BigInt) => BigInt, xs: SCons, ys: SCons): SCons = {
    (xs, ys) match {
      case (SCons(x, _), SCons(y, _)) =>
        SCons(f(x, y), Susp(() => zipWithSusp(f, xs, ys)))
    }
  } ensuring(alloc <= ?) // Orb result: 17

  private def zipWithSusp(f: (BigInt, BigInt) => BigInt, xs: SCons, ys: SCons): SCons = {
    zipWithFun(f, xs.tail, ys.tail)
  }

  /**
   * Given three elements, computes the next element.
   */
  @invisibleBody
  def next(f: SCons, s: SCons, t: SCons): SCons = {
    t.tail
  } ensuring(_ => alloc <= ?) // Orb result: alloc <= 73

  /**
   * Given the first three elements, reading the nth element (s.t. n >= 4) from a
   * `argChainedStream` will take only linear alloc.
   */
  @invisibleBody
  def nthElemAfterThird(n: BigInt, f: SCons, s: SCons, t: SCons): BigInt = {
    next(f, s, t) match {
      case fourth@SCons(x, _) =>
        if (n == 3) x
        else
          nthElemAfterThird(n - 1, s, t, fourth)
    }
  } ensuring(_ => alloc <= ? * n + ?) // Orb result: 84 * n - 167

  /**
   * Using a `zipWithFun` function to implement a fibonacci stream.
   */
  val fibstream: SCons = SCons(0, Val(SCons(1, Susp(() => genNext))))
  @invisibleBody
  def genNext = {
    val fibs = this.fibstream
    zipWithFun(_ + _, fibs, fibs.tail)
  } ensuring(_ => alloc <= ?)

  /**
   * `nth` fib in O(n) alloc.
   */
  def nthFib(n: BigInt) = {
    val first = fibstream
    if(n == 0) first.x
    else{
      val second = first.tail
      if(n == 1) second.x
      else {
        val third = second.tail
        if(n == 2) third.x
        else nthElemAfterThird(n, first, second, third)
      }
    }
  } ensuring(_ => alloc <= ? * n + ?) // Orb result: 84 * n + 6
}