package lazybenchmarks

import leon.lazyeval._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
//import leon.invariant._

object BottomUpMergeSort {

  sealed abstract class IList {
    def size: BigInt = {
      this match {
        case ICons(_, xs) => 1 + xs.size
        case _            => BigInt(0)
      }
    } ensuring (_ >= 0)
  }
  case class ICons(x: BigInt, tail: IList) extends IList
  case class INil() extends IList

  sealed abstract class ILList {
    def size: BigInt = {
      this match {
        case LCons(_, xs) => 1 + ssize(xs)
        case _            => BigInt(0)
      }
    } ensuring (_ >= 0)
  }
  case class LCons(x: BigInt, tail: $[ILList]) extends ILList
  case class LNil() extends ILList
  def ssize(l: $[ILList]): BigInt = (l*).size

  // TODO: making this parametric will break many things. Fix them
  sealed abstract class LList {
    def size: BigInt = {
      this match {
        case SNil()      => BigInt(0)
        case SCons(_, t) => 1 + t.size
      }
    } ensuring (_ >= 0)

    def valid: Boolean = {
      this match {
        case SNil()      => true
        case SCons(l, t) => ssize(l) > 0 && t.valid
      }
    }

    def fullSize: BigInt = {
      this match {
        case SNil()      => BigInt(0)
        case SCons(l, t) => ssize(l) + t.fullSize
      }
    } ensuring (_ >= 0)
  }
  case class SCons(x: $[ILList], tail: LList) extends LList
  case class SNil() extends LList

  // takes O(n) time
  def pairs(l: LList): LList = {
    require(l.valid)
    l match {
      case SNil()           => SNil()
      case SCons(_, SNil()) => l
      case SCons(l1, SCons(l2, rest)) =>
        SCons($(merge(l1, l2)), pairs(rest))
    }
  } ensuring (res => res.size <= (l.size + 1) / 2 &&
    l.fullSize == res.fullSize &&
    res.valid &&
    time <= 10 * l.size + 4)

  def constructMergeTree(l: LList): LList = {
    require(l.valid)
    l match {
      case SNil()           => SNil()
      case SCons(_, SNil()) => l
      case _ =>
        constructMergeTree(pairs(l))
    }
  } ensuring (res => res.size <= 1 && res.fullSize == l.fullSize &&
    (res match {
      case SCons(il, SNil()) =>
        res.fullSize == ssize(il) // this is implied by the previous conditions
      case _ => true
    }) &&
    res.valid &&
    time <= 42 * l.size + 4)

  // here size of res is required to be >= 1
  def merge(a: $[ILList], b: $[ILList]): ILList = {
    require(((a*) != LNil() || b.isEvaluated) && // if one of them is Nil then the other is evaluated
        ((b*) != LNil() || a.isEvaluated) &&
        ((a*) != LNil() || (b*) != LNil())) // one of them is not Nil
    b.value match {
      case LNil() => a.value
      case bl @ LCons(x, xs) =>
        a.value match {
          case LNil() => bl
          case LCons(y, ys) =>
            if (y < x)
              LCons(y, $(merge(ys, b)))
            else
              LCons(x, $(merge(a, xs)))
        }
    }
  } ensuring (res => ssize(a) + ssize(b) == res.size &&
       time <= 300 * res.size - 100)

  // this will take O(n) time
  def IListToLList(l: IList): LList = {
    l match {
      case INil() => SNil()
      case ICons(x, xs) =>
        SCons($(LCons(x, $(LNil()))), IListToLList(xs))
    }
  } ensuring (res => res.fullSize == l.size &&
    res.size == l.size &&
    res.valid &&
    time <= 9 * l.size + 3)

  def mergeSort(l: IList): ILList = {
    l match {
      case INil() => LNil()
      case _ =>
        constructMergeTree(IListToLList(l)) match {
          case SCons(r, SNil()) => r.value
        }
    }
  } ensuring (res => time <= 400 * l.size + 10)

  /**
   * Order statistics
   */
  def firstMin(l: IList) : BigInt ={
    require(l != INil())
    mergeSort(l) match {
      case LCons(x, rest) => x
    }
  } ensuring (res => time <= 400 * l.size + 20)
}
