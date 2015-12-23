import leon.lazyeval._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.lazyeval.$.eagerToLazy
import scala.math.BigInt.int2bigInt
//import leon.invariant._

/**
 * Not the required bound
 */
object Hamming {

  sealed abstract class IList {
    def size: BigInt = {
      this match {
        case SNil()      => BigInt(0)
        case SCons(x, t) => 1 + ssize(t)
      }
    } ensuring (_ >= 0)
  }
  case class SCons(x: BigInt, tail: $[IList]) extends IList
  case class SNil() extends IList
  def ssize(l: $[IList]): BigInt = (l*).size

  sealed abstract class List {
    def size: BigInt = {
      this match {
        case Cons(_, xs) => 1 + xs.size
        case _           => BigInt(0)
      }
    } ensuring (_ >= 0)
  }
  case class Cons(x: BigInt, tail: List) extends List
  case class Nil() extends List

  /**
   * The following implementation of Merge
   * produces a list with out duplicates
   */
  def merge(a: $[IList], b: $[IList]): IList = {
    require(a.isSuspension(mult _) && b.isSuspension(mult _))
    b.value match {
      case SNil() => a.value
      case bl @ SCons(x, xs) =>
        a.value match {
          case SNil() => bl
          case SCons(y, ys) =>
            if (x == y)
              SCons(x, $(merge(ys, xs)))
            else if (y < x)
              SCons(y, $(merge(ys, b)))
            else
              SCons(x, $(merge(a, xs)))
        }
    }
  } ensuring(_ => time <= 100)

  def mult(num: BigInt, l: IList): IList ={
    l match {
      case SNil() => SNil()
      case SCons(x, tail) => SCons(num*x, tail)
    }
  } ensuring(_ => time <= 20)

  def nextElems(n: BigInt): IList = {
    merge(merge($(mult(2, hamming(n-1))), $(mult(3, hamming(n-1)))),
        $(mult(5, hamming(n-1))))
  } //ensuring(_ => time <= )

  /**
   * 'n' is some constant that controls the size.
   * Note: the return list would have at least 'n' elements (and possibly more)
   * but is still finite
   */
   def hamming(n: BigInt): IList = {
    if (n <= 0)
      SNil()
    else
      SCons(1, $(nextElems(n)))
  }

   def kthHamming(k: BigInt, hstream: $[IList]): BigInt = {
     require(k >= 1)
     hstream.value match {
       case SCons(x, _) =>
         if(k == 1)
           x
         else kthHamming(k-1, hstream)
       case SNil() =>
         BigInt(-1)
     }
   } //ensuring(_ => time <= 40 * k + 40)
}
