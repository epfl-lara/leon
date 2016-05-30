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
  case class Val(x: SCons) extends ValOrSusp
  case class Susp(fun: () => SCons) extends ValOrSusp

  /**
   * A generic higher-order `zipWithFun` function
   */
  def zipWithFun(f: (BigInt, BigInt) => BigInt, xs: SCons, ys: SCons): SCons = {
    (xs, ys) match {
      case (SCons(x, _), SCons(y, _)) =>
        SCons(f(x, y), Susp(() => zipWithSusp(f, xs, ys)))
    }
  } ensuring(time <= ?) // Orb result: 17

  def zipWithSusp(f: (BigInt, BigInt) => BigInt, xs: SCons, ys: SCons): SCons = {
    zipWithFun(f, xs.tail, ys.tail)
  }


  /**
   * First two elements have been evaluated
   */
  @inline  
  def firstThreeEval(first: SCons, second: SCons, third: SCons) = {
    first.tailVal == second && second.tailVal == third &&  
        first.tailCached && second.tailCached 
  }
  
  /**
   * Given three elements, computes the next element.
   */
  @invisibleBody
  def next(f: SCons, s: SCons, t: SCons): SCons = {
    t.tail 
  }

  @invisibleBody
  def nthElemAfterThird(n: BigInt, f: SCons, s: SCons, t: SCons): BigInt = {
    next(f, s, t) match {
      case fourth@SCons(x, _) =>
        if (n == 3) x
        else
          nthElemAfterThird(n - 1, s, t, fourth)
    }
  }

  /**
   * Using a `zipWithFun` function to implement a fibonacci stream.
   */
  val fibstream: SCons = SCons(0, Val(SCons(1, Susp(() => genNext))))
  @invisibleBody
  val genNext = {
    val fibs = this.fibstream
    zipWithSusp(_ + _, fibs, fibs.tail)
  } ensuring(_ => time <= ?)

  /**
   * `nth` fib in O(n) time.
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
  }
}