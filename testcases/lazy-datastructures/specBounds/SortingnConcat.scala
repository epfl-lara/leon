package sortconcat

import leon._
import mem._
import higherorder._
import lang._
import annotation._
import instrumentation._
import invariant._

object SortingnConcat {

  sealed abstract class LList {
    @inline
    def isEmpty: Boolean = this == SNil()

    lazy val tail: LList = {
      require(!isEmpty)
      this match {
        case SCons(_, tailFun, _) => tailFun()
      }
    }

    def size = this match {
      case SCons(_, _, r) => r
      case SNil()         => BigInt(0)
    }

    /**
     * A property that is true if `sz` field decreases for the tail of the stream.
     * `sz` is a well-founded ordering.
     */
    /*def valid: Boolean = {
      this match {
        case c @ SCons(_, _, r) =>
          r >= 1 && r == (c.tail*).size + 1 && (c.tail*).valid
        case _ => true
      }
    }*/
  }
  private case class SCons(x: BigInt, tailFun: () => LList, sz: BigInt) extends LList
  private case class SNil() extends LList

  sealed abstract class List[T] {
    val size: BigInt = {
      this match {
        case Nil()      => BigInt(0)
        case Cons(_, t) => 1 + t.size
      }
    } ensuring (_ >= 0)
  }
  case class Cons[T](x: T, tail: List[T]) extends List[T]
  case class Nil[T]() extends List[T]

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
        SCons(x, () => sort(xs), l.size) // sorts lazily only if needed
      case _ =>
        SNil()
    }
  } ensuring (res => /*res.valid && */res.size == l.size && steps <= ? * l.size + ?)

/*  def concat(l1: List[BigInt], l2: LList) : LList = {
    l1 match {
      case Cons(x, xs) => SCons(x, Stream(() => concat(xs, l2)))
      case Nil() => SNil()
    }
  } ensuring(res => time <= ?)*/

  def kthMin(l: LList, k: BigInt): BigInt = {
    require(/*l.valid &&*/ k >= 1)
    l match {
      case c@SCons(x, _, _) =>
        if (k == 1) x
        else
          kthMin(c.tail, k - 1) // here, k itself is a ranking function.
      case SNil() => BigInt(0)
    }
  } //ensuring (_ => steps <= ? * (k * l.size) + ? * k + ?)
}