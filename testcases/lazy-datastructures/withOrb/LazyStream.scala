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
  def genZeroNext: SCons = {
    SCons(0, Susp(() => genZeroNext))
  } ensuring(_ => time <= ?) // Orb result: time <= 3

  /**
   * Get the nth elem from a given stream
   */
  @invisibleBody
  def getnthElem(n: BigInt, f: SCons): BigInt = {
    require(n >= 0)
    if(n == 0) f.x
    else getnthElem(n-1, f.tail)
  } ensuring(_ => time <= ? * n + ?) // Orb result: time <=  27 * n + 4

  /**
   * wrapper for the getnthZero function
   */
  def nthZero(n: BigInt) = {
    require(n >= 0)
    val zeros = zeroStream
    getnthElem(n, zeros)
  } ensuring(_ => time <= ? * n + ?) // Orb result: time <= 27 * n + 6 

  /**
   * An integer list data-structure
   */
  sealed abstract class IList {
    def size: BigInt = {
      this match {
        case Cons(_, tail) => 1 + tail.size
        case Nil() => BigInt(0)
      }
    } ensuring(_ >= 0)
  }
  case class Cons(x: BigInt, tail: IList) extends IList
  case class Nil() extends IList

  /** 
   * The function lazyappend appends a list to a stream, 
   * returning a stream of all the list elements
   * followed by all the original stream elements.
   */
  def lazyappend(l: IList, s: SCons): SCons = {
    l match {
      case Nil() => s
      case Cons(x, tail) => SCons(x, Susp(() => lazyappend(tail, s)))
    }
  } ensuring(_ => time <= ? * l.size + ?) // Orb result: ??

  /** 
   * The function repeat expects a list and returns a 
   * stream that represents infinite appends of the
   * list to itself.
   */
  def repeat(l: IList): SCons = {
    lazyappend(l, repeat(l))
  } ensuring(_ => time <= ?) // Orb result: ??

  def nthElemInRepeat(n: BigInt, l: IList) = {
    require(n >= 0)
    val rstream = repeat(l)
    if(n == 0) rstream.x
    else getnthElem(n, rstream)
  } ensuring(_ => time <= ? * n + ?) // Orb result: ??

  /**
   * Stream for all natural numbers starting from n
   *
   */
  val nats: SCons = SCons(0, Susp(() => genNextNatFrom(0)))

  @invisibleBody
  def genNextNatFrom(n: BigInt): SCons = {
    require(n >= 0)
    SCons(n + 1, Susp(() => genNextNatFrom(n + 1)))
  } ensuring(_ => time <= ?) // Orb result: ??

  def nthElemInNats(n: BigInt) = {
    require(n >= 0)
    val natstream = nats
    if(n == 0) natstream.x
    else getnthElem(n, natstream)
  } ensuring(_ => time <= ? * n + ?) // Orb result: ??

}
