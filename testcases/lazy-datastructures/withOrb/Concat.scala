package withOrb

import leon._
import lazyeval._
import lazyeval.Lazy._
import lang._
import annotation._
import instrumentation._
import collection._
import invariant._

object Concat {
  sealed abstract class LList[T] {
    def size: BigInt = {
      this match {
        case SNil()      => BigInt(0)
        case SCons(x, t) => 1 + ssize(t)
      }
    } ensuring (_ >= 0)
  }
  case class SCons[T](x: T, tail: Lazy[LList[T]]) extends LList[T]
  case class SNil[T]() extends LList[T]
  def ssize[T](l: Lazy[LList[T]]): BigInt = (l*).size

  def concat[T](l1: List[T], l2: List[T]): LList[T] = {
    l1 match {
      case Cons(x, xs) => SCons(x, $(concat(xs, l2)))
      case Nil()       => SNil[T]()
    }
  } ensuring { _ => time <= ? }

  def kthElem[T](l: Lazy[LList[T]], k: BigInt): Option[T] = {
    require(k >= 0)
    l.value match {
      case SCons(x, xs) =>
        if (k == 0) Some(x)
        else
          kthElem(xs, k - 1)
      case SNil() => None[T]
    }
  } ensuring (_ => time <= ? * k + ?)

  def concatnSelect[T](l1: List[T], l2: List[T], k: BigInt): Option[T] = {
    require(k >= 0)
    kthElem($(concat(l1, l2)), k)
  } ensuring (_ => time <= ? * k + ?)

  @ignore
  def main(args: Array[String]) = {
    import stats._
    println("Running concat test...")
    val length = 1000000
    val k = 10
    val iterCount = 10
    val l1 = (0 until length).foldRight(List[BigInt]()) {
      case (i, acc) => i :: acc
    }
    val l2 = (0 until length).foldRight(List[BigInt]()) {
      case (i, acc) => 2 * i :: acc
    }
    println("Created inputs, starting operations...")
    def iterate[T](op: => BigInt) = {
      var res = BigInt(0)
      var i = iterCount
      while (i > 0) {
        res = op
        i -= 1
      }
      res
    }
    val elem1 = timed { iterate((l1 ++ l2)(k)) } { t => println(s"Eager Concat completed in ${t / 1000.0} sec") }
    println(s"$k th element of concatenated list: $elem1")
    val elem2 = timed { iterate(concatnSelect(l1, l2, k).get) } { t => println(s"Lazy ConcatnSelect completed in ${t / 1000.0} sec") }
    println(s"$k th element of concatenated list: $elem2")
    assert(elem1 == elem2)
  }
}
