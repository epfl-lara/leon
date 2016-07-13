package withOrb

import leon._
import mem._
import higherorder._
import lang._
import annotation._
import instrumentation._
import invariant._
import collection._

object SortingnConcat {

  sealed abstract class LList {
    def size: BigInt = {
      this match {
        case SCons(_, t) => 1 + t.size
        case _            => BigInt(0)
      }
    } ensuring (_ >= 0)
  }
  private case class SCons(x: BigInt, tailFun: Stream) extends LList
  private case class SNil() extends LList
  private case class Stream(lfun: () => LList) {
    lazy val list: LList = lfun()
    @inline
    def size = (list*).size
  }

  def pullMin(l: List[BigInt]): List[BigInt] = {
    l match {
      case Nil() => l
      case Cons(x, xs) =>
        pullMin(xs) match {
          case Nil() => Cons(x, Nil())
          case nxs @ Cons(y, ys) =>
            if (x <= y) Cons(x, nxs)
            else Cons(y, Cons(x, ys))
        }
    }
  } ensuring (res => res.size == l.size && steps <= ? * l.size + ?)

  def sort(l: List[BigInt]): LList = {
    pullMin(l) match {
      case Cons(x, xs) =>
        // here, x is the minimum
        SCons(x, Stream(() => sort(xs))) // sorts lazily only if needed
      case _ =>
        SNil()        
    }
  } ensuring (res => res.size == l.size && steps <= ? * l.size + ?)

  def concat(l1: List[BigInt], l2: LList) : LList = {
    l1 match {
      case Cons(x, xs) => SCons(x, Stream(() => concat(xs, l2)))
      case Nil() => SNil()
    }
  } ensuring(res => steps <= ?)

  def kthMin(l: Stream, k: BigInt): BigInt = {
    require(k >= 1)
    l.list match {
      case SCons(x, xs) =>
        if (k == 1) x
        else
          kthMin(xs, k - 1)
      case SNil() => BigInt(0)
    }
  } ensuring (_ => steps <= ? * (k * l.size) + ? * k + ?)
}
