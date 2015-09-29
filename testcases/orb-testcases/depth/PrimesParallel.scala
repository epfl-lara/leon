import leon.instrumentation._
import leon.invariant._
import leon.annotation._

object PrimesParallel {
  sealed abstract class List
  case class Cons(head: BigInt, tail: List) extends List
  case class Nil() extends List

  def size(l: List): BigInt = (l match {
    case Nil() => 0
    case Cons(_, t) => 1 + size(t)
  })

  //a program that removes from a list, all multiples of a number 'i' upto 'n'
  //the depth of this program is again 1
//  def removeMultiples(l: List, i: BigInt, n: BigInt, incr: BigInt): (List, BigInt) = {
//    require(i >= 0 && incr >= 1 && i <= n)
//    l match {
//      case Nil() => (Nil(), 0)
//      case Cons(x, t) => {
//        if (x < i) {
//          val (r,d) = removeMultiples(t, i, n, incr)
//          (Cons(x, r), max(d, 2))
//
//        } else if (x > i) {
//          val ni = i + incr
//          if (ni > n) (l, 2)
//          else {
//            val (r,d) = removeMultiples(l, ni, n, incr)
//            (r, max(d, 2))
//          }
//
//
//        } else {
//          val ni = i + incr
//          if (ni > n) (t, 2)
//          else{
//            val (r,d) = removeMultiples(l, ni, n, incr)
//            (r, max(d, 2))
//          }
//        }
//      }
//    }
//  } //ensuring (res => true && tmpl ((a) => res._2 <= a))
  //ensuring (res => true && tmpl ((a,b) => time <= a*(size(l) + n - i) + b))

  //another function with constant depth
//  def createList(i: BigInt, n: BigInt) : (List, BigInt) = {
//    require(i <= n)
//    if(n == i) (Nil(), 0)
//    else {
//      val (r, d) = createList(i+1, n)
//      (Cons(i, r), max(d, 2))
//    }
//  } //ensuring(res => true && tmpl((a) => res._2 <= a))
  //ensuring(res => true && tmpl((a,b) => time <= a*(n-i) + b))

//  def removeNonPrimes(currval: BigInt, l: List, n: BigInt, sqrtn: BigInt): (List, BigInt) = {
//    require(currval <= sqrtn && sqrtn <= n && currval >= 1)
//
//    val (r,d) = removeMultiples(l, currval, n, currval)
//    if(currval == sqrtn) {
//      (r, d + 2)
//    } else {
//      val (res, t) = removeNonPrimes(currval + 1, r, n, sqrtn)
//      (res, t + 2)
//    }
//  } //ensuring(res => true && tmpl((a,b) => res._2 <= a*(sqrtn - currval) + b))

//  def simplePrimes(n: BigInt, sqrtn : BigInt) : (List, BigInt) = {
//    require(sqrtn >= 2 && sqrtn <= n)
//
//     val (l, d1) = createList(2, n)
//     val (resl, t2) = removeNonPrimes(2, l, n, sqrtn)
//     (resl, d1 + t2 + 3)
//  }  //ensuring(res => true && tmpl((a,b) => res._2 <= a*sqrtn + b))
}
