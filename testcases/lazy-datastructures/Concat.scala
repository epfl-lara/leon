import leon.lazyeval._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.collection._
//import leon.invariant._

object Concat {
  sealed abstract class LList[T] {
    def size: BigInt = {
      this match {
        case SNil()      => BigInt(0)
        case SCons(x, t) => 1 + ssize(t)
      }
    } ensuring (_ >= 0)
  }
  case class SCons[T](x: T, tail: $[LList[T]]) extends LList[T]
  case class SNil[T]() extends LList[T]
  def ssize[T](l: $[LList[T]]): BigInt = (l*).size

  def concat[T](l1: List[T], l2: List[T]) : LList[T] = {
    l1 match {
      case Cons(x, xs) => SCons(x, $(concat(xs, l2)))
      case Nil() => SNil[T]()
    }
  } ensuring(_ => time <= 15)

  def kthElem[T](l: $[LList[T]], k: BigInt): Option[T] = {
    require(k >= 1)
    l.value match {
      case SCons(x, xs) =>
        if (k == 1) Some(x)
        else
          kthElem(xs, k - 1)
      case SNil() => None[T]
    }
  } ensuring (_ => time <= 40 * k)

  def concatnSelect[T](l1: List[T], l2: List[T], k: BigInt) : Option[T] = {
    require(k >= 1)
    kthElem($(concat(l1, l2)), k)
  } ensuring (_ => time <= 50 * k)
}
