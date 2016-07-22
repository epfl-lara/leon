package withOrb

import leon._
import mem._
import higherorder._
import lang._
import annotation._
import instrumentation._
import collection._
import invariant._

object Concat {
  sealed abstract class LList[T] {
    lazy val tail = {
      require(this != SNil[T]())
      this match {
        case SCons(_, tfun) => tfun()
      }
    }
    
    def size: BigInt = {
      this match {
        case SNil()      => BigInt(0)
        case SCons(x, _) => 1 + (tail*).size
      }
    } ensuring (_ >= 0)
  }
  private case class SCons[T](x: T, tailFun: () => LList[T]) extends LList[T]            
  private case class SNil[T]() extends LList[T]  

  def concat[T](l1: List[T], l2: List[T]): LList[T] = {
    l1 match {
      case Cons(x, xs) => SCons(x, () => concat(xs, l2))
      case Nil()       => SNil[T]()
    }
  } ensuring { _ => steps <= ? }

  def kthElem[T](l: LList[T], k: BigInt): Option[T] = {
    require(k >= 0)
    l match {
      case SCons(x, _) =>
        if (k == 0) Some(x)
        else
          kthElem(l.tail, k - 1)
      case SNil() => None[T]
    }
  } ensuring (_ => steps <= ? * k + ?)

  def concatnSelect[T](l1: List[T], l2: List[T], k: BigInt): Option[T] = {
    require(k >= 0)
    kthElem(concat(l1, l2), k)
  } ensuring (_ => steps <= ? * k + ?)

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
