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
 * This file is the collection of programs in the ESOP 2015 paper.
 * Note this benchmark is very good for finding counter-examples.s
 * Decreasing the time bounds slightly will display counter-examples.
 */
object Esop15Benchmarks {
  /*sealed abstract class Stream[T] {
    lazy val tail = {
      require(this != SNil())
      this match {
        case SCons(_, tailfun) => tailfun()
      }
    }
  }*/
  case class SCons[T](x: T, tail: ValOrSusp[T])

  sealed abstract class ValOrSusp[T] {
    def isCached = this match {
      case Val(_) => true
      case _ => get.cached
    }

    /*def isSusp = this match {
      case Val(_) => false
      case _ =>  true
    }*/

    lazy val get = {
      this match {
        case Val(x) => x
        case Susp(f) => f()
      }
    }
  }
  case class Val[T](x: SCons[T]) extends ValOrSusp[T]
  case class Susp[T](fun: () => SCons[T]) extends ValOrSusp[T]

  lazy val fibstream: SCons[BigInt] =
    SCons[BigInt](0, Val(SCons[BigInt](1, Val(SCons[BigInt](1, Susp(() => fibStreamGen))))))

  def fibStreamGen: SCons[BigInt] = {
    val fibs = this.fibstream
    fibs match {
      case s @ SCons(x, _) => zipWithFun((x: BigInt, y: BigInt) => x + y, fibs, s.tail.get)
    }
  } ensuring(_ => time <= ?)

  @invstate
  def zipWithFun(f: (BigInt, BigInt) => BigInt, xs: SCons[BigInt], ys: SCons[BigInt]): SCons[BigInt] = {
    require(xs.tail.isCached && ys.tail.isCached)
    (xs, ys) match {
      case (SCons(x, _), SCons(y, _)) =>
        val xtail = xs.tail.get
        val ytail = ys.tail.get
        SCons[BigInt](f(x, y), Susp(() => zipWithFun(f, xtail, ytail)))
    }
  } ensuring { _ =>
//    /if (isCached(xs, ys, inState[BigInt]))
      time <= ?
    //else true
  }

  /**
   * Checks if `xs.tail` and `ys.tail` have been evaluated in the state `st`
   */
  /*def isCached(xs: SCons[BigInt], ys: SCons[BigInt], st: Set[Fun[BigInt]]) = {
    (xs, ys) match {
      case (SCons(_, _), SCons(_, _)) => (xs.tail.isCached withState st) && (ys.tail.isCached withState st)
      case _ => true
    }
  }*/

  def nthElem(n: BigInt, fibs: SCons[BigInt]): BigInt = {
    require(n >= 0)
    fibs match {
      case SCons(x, _) =>
        if (n == 0) x
        else
          nthElem(n - 1, fibs.tail.get)
    }
  } ensuring(_ => time <= ? * n + ?)

  /*def nextFib(x: BigInt, y: BigInt, n: BigInt): IStream = {
    if (n <= 0)
      SNil()
    else {
      val next = x + y
      SCons(next, $(nextFib(y, next, n - 1)))
    }
  } ensuring(_ => time <= ?)

  def fibStream(n: BigInt) : IStream = {
    SCons(0, SCons(1, $(nextFib(0, 1, n))))
  }

  def nthFib(n: BigInt, fs: Lazy[IStream]): BigInt = {
    require(n >= 0)
    fs.value match {
      case SCons(x, tail) =>
        if (n == 0)
          x
        else
          nthFib(n - 1, tail)
      case SNil() => BigInt(-1)
    }
  } ensuring(_ => time <= ? * n + ?) // you get a counter-example for 20*n + 20
*/ }