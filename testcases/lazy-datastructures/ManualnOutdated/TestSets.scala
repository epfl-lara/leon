package ManualnOutdated

import leon.lazyeval._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
//import leon.invariant._

object TestSets {

  sealed abstract class List[T] {
    def size: BigInt = {
      this match {
        case SNil()      => BigInt(0)
        case SCons(x, t) => 1 + t.size
      }
    } ensuring (_ >= 0)
  }
  case class SCons[T](x: T, tail: List[T]) extends List[T]
  case class SNil[T]() extends List[T]

  def concat[T](l1: List[T], l2: List[T], st: Set[T]) : List[T] = {
    l1 match {
      case SCons(x, xs) => SCons(x, concat(xs, l2, st ++ Set[T](x)))
      case SNil() => SNil[T]()
    }
  } ensuring(res => time <= ? * l1.size + ?)
}
