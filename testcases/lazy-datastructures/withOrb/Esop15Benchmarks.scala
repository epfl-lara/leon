package withorb

import leon._
import lang._
import annotation._
import instrumentation._
import mem._
import higherorder._
import collection._
import invariant._

object ZipWithAndFibStream {
  /**
   *  An infinite integer stream.
   *  Technically, the data structure is *not* infinite but the tail is has a higher-order function.
   */
  case class SCons(x: BigInt, tail: ValOrSusp)

  sealed abstract class ValOrSusp {
    def isCached = this match {
      case Val(_) => true
      case _ => fval.cached
    }

    def get = {
      this match {
        case Susp(f) => fval
        case Val(x) => x
      }
    }

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
    zipWithFun(f, xs.tail.get, ys.tail.get)
  }

  /**
   * Properties of `zipWithFun`. In fact, they are generalizable beyond `zipWithFun`.
   */
  /**
   * Holds if for given a stream `s`, s.tail.tail is a suspension of `zipWithSusp` applied over `s` and `s.tail`.
   */
  def argChainingProp(s: SCons): Boolean = {
    val stail = (s.tail.get*)
    stail.tail match {
      case Susp(tailfun) =>
        tailfun fmatch[(BigInt, BigInt) => BigInt, SCons, SCons, Boolean] {
          case (f, xs, ys) if (tailfun.is(() => zipWithSusp(f, xs, ys))) =>
            (xs == s && ys == stail)
          case _ => false
        }
      case _ => false
    }
  }

  /**
   * States that `argChaining` property holds for every sub-stream until a limit `n`
   * (note: this method could generalized to a co-recursive function)
   */
  def argChainedStreamProp(s: SCons, n: BigInt): Boolean = {
    require(n >= 0)
    argChainingProp(s) &&
    (if(n == 0) true
    else {
     argChainedStreamProp(s.tail.get*, n - 1)
    })
  }

  @inline
  def inductionScheme(fibs: SCons, n: BigInt): Boolean = {
    val fibTail = (fibs.tail.get*)
    (fibTail.tail match {
      case Val(_) => true
      case Susp(tailfun) =>
        tailfun.fmatch[(BigInt, BigInt) => BigInt, SCons, SCons, Boolean] {
          case (f, xs, ys) if (tailfun.is(() => zipWithSusp(f, xs, ys))) =>
            argChainingIsTransitive(fibTail, n)
          case _ => true
        }
    })
  }

  def argChainingIsTransitive(fibs: SCons, n: BigInt): Boolean = {
    require(n >= 0 && argChainingProp(fibs))
    inductionScheme(fibs, n) && argChainedStreamProp(fibs, n)
  } holds

  /**
   * Reading the nth element from a `argChainedStream` will take only linear time.
   */
  def nthElem(n: BigInt, s: SCons): BigInt = {
    require(n >= 0 && s.tail.isCached && argChainedStreamProp(s, n))
    s match {
      case SCons(x, _) =>
        if (n == 0) x
        else
          nthElem(n - 1, s.tail.get)
    }
  } ensuring(_ => time <= ? * n + ?) // Orb result: 23 * n + 6

  /**
   * Using a `zipWithFun` function to implement a fibonacci stream.
   */
  val fibstream: SCons = SCons(0, Val(SCons(1, Susp(() => {
    val fibs = this.fibstream
    zipWithSusp(_ + _, fibs, fibs.tail.get)
  }))))

  /**
   * Establishes that `fibstream` satisfies `argChainedStream` property.
   */
  def fibStreamSastisfiesProp(n: BigInt): Boolean = {
    require(n >= 0)
    val fibs = fibstream
    argChainingIsTransitive((fibs.tail.get*), n) &&
      argChainedStreamProp(fibs, n)
  } holds

  /**
   * `nth` fib in O(n) time.
   */
  def nthFib(n: BigInt) = {
    require(n >= 0 && fibStreamSastisfiesProp(n))
    nthElem(n, fibstream)
  } ensuring(_ => time <= ? * n + ?) // Orb result: 23 * n + 8
}