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
        case Val(x)  => x
      }
    }
  }
  case class Val(x: LList) extends ValOrSusp
  case class Susp(fun: () => LList) extends ValOrSusp

  /**
   *  An infinite integer stream.
   *  Technically, the data structure is *not* infinite but the tail has a higher-order function.
   */
  sealed abstract class LList {
    //@inline
    def tail = {
      require(this != SNil())
      val SCons(x, tailFun) = this
      tailFun match {
        case s @ Susp(f) => s.fval
        case Val(x)      => x
      }
    }

    def tailOrNil = {
      this match {
        case SNil() => this
        case SCons(x, tailFun) =>
          tailFun match {
            case s @ Susp(f) => s.fval
            case Val(x)      => x
          }
      }
    }

    // this will not modify state
    def tailVal = {
      require(this != SNil())
      val SCons(x, tailFun) = this
      tailFun match {
        case s @ Susp(f) => s.fval*
        case Val(x)      => x
      }
    }

    //@inline
    def tailCached = {
      require(this != SNil())
      val SCons(x, tailFun) = this
      tailFun match {
        case Val(_) => true
        case s      => s.fval.cached
      }
    }
  }
  case class SCons(x: BigInt, tailFun: ValOrSusp) extends LList
  case class SNil() extends LList

  /**
   * Get the nth elem from a given stream
   */
  @invisibleBody
  def getnthElem(n: BigInt, f: LList): BigInt = {
    require(n >= 0)
    f match {
      case SNil() => BigInt(0)
      case s @ SCons(x, _) =>
        if (n == 0) x
        else getnthElem(n - 1, s.tailOrNil)
    }
  } ensuring (_ => time <= ? * n + ?) // Orb result: time <=  27 * n + 4

  /**
   * Stream for all natural numbers starting from n
   */
  val nats = SCons(0, Val(genNextNatFrom(0)))
  @invisibleBody
  def genNextNatFrom(n: BigInt): LList = {
    val nn = n + 1
    SCons(n + 1, Susp(() => genNextNatFrom(nn)))
  } ensuring(res => time <= ?) // Orb result: ??

  def natStream(s: LList): Boolean = {
    s match {
      case SCons(_, Susp(tailFun)) =>
        tailFun fmatch[BigInt, Boolean] {
          case n if tailFun.is(() => genNextNatFrom(n)) => true
          case _ => false
        }
      case SCons(_, Val(st)) => natStream(st)
      case _ => true
    }
  }

  def map(f: BigInt => BigInt, s: LList): LList = {
    require(natStream(s))
    s match {
      case SNil()          => SNil()
      case l @ SCons(x, _) => SCons(f(x), Susp(() => mapSusp(f, s)))
    }
  } ensuring (_ => time <= ?)

  @invisibleBody
  def mapSusp(f: BigInt => BigInt, s: LList) = {
    require(natStream(s))
    map(f, s.tailOrNil)
  } ensuring(_ => time <= ?)
}
