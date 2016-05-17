package stream

import leon._
import lang._
import annotation._
import instrumentation._
import mem._
import higherorder._
import collection._
import invariant._

object StreamLibrary {
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
  case class Val(x: LList) extends ValOrSusp
  case class Susp(fun: () => LList) extends ValOrSusp

  /**
   *  An infinite integer stream.
   *  Technically, the data structure is *not* infinite but the tail has a higher-order function.
   */
  sealed abstract class LList
  case class SCons(x: BigInt, tailFun: ValOrSusp) extends LList {
    //@inline
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
  case class SNil() extends LList

  /**
   * Get the nth elem from a given stream
   */
  @invisibleBody
  def getnthElem(n: BigInt, f: LList): BigInt = {
    require(n >= 0)
    f match {
      case SNil() => BigInt(0)
      case s@SCons(x, _) =>
        if(n == 0) x
        else getnthElem(n-1, s.tail)
    }
  } ensuring(_ => time <= ? * n + ?) // Orb result: time <=  27 * n + 4
}
