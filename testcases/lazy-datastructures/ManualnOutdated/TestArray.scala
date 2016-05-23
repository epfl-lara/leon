package ManualnOutdated

import leon.lazyeval._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import scala.math.BigInt.int2bigInt
//import leon.invariant._

object TestArray {

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

  def concat(l1: List, l2: LList) : LList = {
    l1 match {
      case Cons(x, xs) => SCons(x, $(concat(xs, l2)))
      case Nil() => SNil()
    }
  } ensuring(res => time <= 15)

  @ignore
  var arr = Array[BigInt]()

  @extern
  def arrayFun(l1: List, l2: LList, i: BigInt): BigInt = {
    //require(i >= 0)
    //Array(concat(l1, l2))
    arr(i.toInt)
  }
}
