package withOrb

import leon.lazyeval._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._

object SortingnConcat {

  // TODO: making this parametric will break many things. Fix them
  sealed abstract class LList {
    def size: BigInt = {
      this match {
        case SNil()      => BigInt(0)
        case SCons(x, t) => 1 + ssize(t)
      }
    } ensuring (_ >= 0)
  }
  case class SCons(x: BigInt, tail: $[LList]) extends LList
  case class SNil() extends LList
  def ssize(l: $[LList]): BigInt = (l*).size

  sealed abstract class List {
    def size: BigInt = this match {
      case Cons(_, xs) => 1 + xs.size
      case _           => BigInt(0)
    }
  }
  case class Cons(x: BigInt, tail: List) extends List
  case class Nil() extends List

  def pullMin(l: List): List = {
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
  } ensuring (res => res.size == l.size && time <= ? * l.size + ?)

  def sort(l: List): LList = {
    pullMin(l) match {
      case Cons(x, xs) =>
        // here, x is the minimum
        SCons(x, $(sort(xs))) // sorts lazily only if needed
      case _ =>
        SNil()
    }
  } ensuring (res => res.size == l.size && time <= ? * l.size + ?)

  def concat(l1: List, l2: LList) : LList = {
    l1 match {
      case Cons(x, xs) => SCons(x, $(concat(xs, l2)))
      case Nil() => SNil()
    }
  } ensuring(res => time <= ?)

  def secondMin(l: $[LList]) : BigInt = {
    l.value match {
      case SCons(x, xs) =>
        xs.value match {
          case SCons(y, ys) => y
          case SNil() => x
        }
      case SNil() => BigInt(0)
    }
  } ensuring (_ => time <= ? * ssize(l) + ?)

  // Orb can prove this
  def kthMin(l: $[LList], k: BigInt): BigInt = {
    require(k >= 1)
    l.value match {
      case SCons(x, xs) =>
        if (k == 1) x
        else
          kthMin(xs, k - 1)
      case SNil() => BigInt(0) // None[BigInt]
    }
  } ensuring (_ => time <= ? * k * ssize(l) + ? * k + ?)
}
