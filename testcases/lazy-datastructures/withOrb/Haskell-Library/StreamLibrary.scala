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
  def natsFromn(n: BigInt) = {
    SCons(n, Susp(() => genNextNatFrom(n)))
  }

  def validNatStream(s: LList): Boolean = {
    s match {
      case SCons(_, Susp(tailFun)) =>
        tailFun fmatch[BigInt, Boolean] {
          case n if tailFun.is(() => genNextNatFrom(n)) => true
          case _ => false
        }
      case SCons(_, Val(st)) => validNatStream(st)
      case _ => true
    }
  }

  @invisibleBody
  def genNextNatFrom(n: BigInt): LList = {
    val nn = n + 1
    SCons(nn, Susp(() => genNextNatFrom(nn)))
  } ensuring(_ => time <= ?) // Orb result: ??

  def nthElemInNatsFromM(n: BigInt, M: BigInt) = {
    require(n >= 0)
    getnthElem(n, natsFromn(M))
  } ensuring(_ => time <= ? * n + ?) // Orb result: ??

  /**
   * Apply a function uniformly over all elements of a sequence.
   */
  def map(f: BigInt => BigInt, s: LList): LList = {
    require(validNatStream(s))
    s match {
      case SNil()          => SNil()
      case l @ SCons(x, _) => SCons(f(x), Susp(() => mapSusp(f, s)))
    }
  } ensuring (_ => time <= ?)

  @invisibleBody
  def mapSusp(f: BigInt => BigInt, s: LList) = {
    require(validNatStream(s))
    map(f, s.tailOrNil)
  } ensuring(_ => time <= ?)

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
   * The function repeat expects an integer and returns a
   * stream that represents infinite appends of the
   * integer to itself.
   */
  def repeat(n: BigInt): LList = {
    SCons(n, Susp(() => repeat(n)))
  } ensuring (_ => time <= ?) // Orb result: ??

  /**
   * The function cycle expects a list and returns a
   * stream that represents infinite appends of the
   * list to itself.
   */
  def cycle(l: List[BigInt]): LList = {
    l match {
      case Nil() => SNil()
      case Cons(x, t) =>
        SCons(x, Susp(() => lazyappend(t, cycle(l))))
    }
  } ensuring (_ => time <= ?) // Orb result: ??

  /**
   * 'scan' yields a stream of successive reduced values from:
   *  scan f z [x1, x2, ...] == [z, z `f` x1, (z `f` x1) `f` x2, ...]
   */
  // def scan(f: (BigInt, BigInt) => BigInt, z: BigInt, s: LList): LList = {
  //   require(validNatStream(s))
  //   s match {
  //     case SNil()          => SNil()
  //     case l @ SCons(x, _) => SCons(z, Susp(() => scanSusp(f, f(z, x), s)))
  //   }
  // } ensuring (_ => time <= ?)

  // @invisibleBody
  // def scanSusp(f: (BigInt, BigInt) => BigInt, z: BigInt, s: LList) = {
  //   require(validNatStream(s))
  //   scan(f, z, s.tailOrNil)
  // } ensuring(_ => time <= ?)

  /**
   * 'takeWhile' returns the longest prefix of the stream for which the 
   * predicate p holds.
   */
  def takeWhile(p: BigInt => Boolean, s: LList): List[BigInt] = {
    require(validNatStream(s))
    s match {
      case SNil()          => Nil()
      case l @ SCons(x, _) => {
        if(p(x)) Cons(x, takeWhile(p, s.tailOrNil))
        else takeWhile(p, s.tailOrNil)
      }
    }
  } ensuring (_ => time <= ?)

  // @invisibleBody
  // def takeWhileSusp(p: BigInt => Boolean, s: LList): List[BigInt] = {
  //   require(validNatStream(s))
  //   takeWhile(p, s.tailOrNil)
  // } ensuring(_ => time <= ?)


}
