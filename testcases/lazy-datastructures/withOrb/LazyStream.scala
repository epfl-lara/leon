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
 * Hint: requires unrollfactor=4, as of now this example works with 2
 */
object LazyStream {
  /**
  * A placeholder in a stream is either a Val or a Susp()
  */
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

  /**
   * Implementing an infinite stream of zeroes
   */
  val zeroStream: SCons = SCons(0, Susp(() => genZeroNext))

  @invisibleBody
  val genZeroNext: SCons = {
    SCons(0, Susp(() => genZeroNext))
  } ensuring(_ => time <= ?)

  /**
   * Get the nth zero from a given zeroStream
   */
  @invisibleBody
  def getnthZero(n: BigInt, f: SCons): BigInt = {
    require(n >= 0)
    if(n == 0) f.x
    else getnthZero(n-1, f.tail)
  } ensuring(_ => time <= ? * n + ?) // Orb result: time <=  27 * n + 4

  /**
   * wrapper for the getnthZero function
   */
  def nthZero(n: BigInt) = {
    require(n >= 0)
    val first = zeroStream
    getnthZero(n, first)
  } ensuring(_ => time <= ? * n + ?) // Orb result: 27 * n + 6 
}