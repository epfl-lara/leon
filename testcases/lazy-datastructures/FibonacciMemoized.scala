package lazybenchmarks

import leon.lazyeval._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
//import leon.invariant._

object FibMem {

  /**
   * A simple non-lazy list of integers
   */
  sealed abstract class IList
  case class Cons(x: BigInt, tail: IList) extends IList
  case class Nil() extends IList

  def fibRec(n: BigInt): BigInt = {
    require(n <= 2 || ($(fibRec(n-1)).isEvaluated && // previous two values have been evaluated
        $(fibRec(n-2)).isEvaluated))
        if(n <= 2)
          BigInt(1)
        else
          fibRec(n-1) + fibRec(n-2)
  } ensuring(_ => time <= 50)

  def fibRange(i: BigInt, k: BigInt): IList = {
    require(k >= 1 && i <= k &&
        (i <= 1 ||
        (($(fibRec(i-1)).isEvaluated) &&
            (i <= 2 || $(fibRec(i-2)).isEvaluated))))
    if(i == k)
      Cons(fibRec(i), Nil())
    else {
      val x = $(fibRec(i)).value
      Cons(x, fibRange(i + 1, k))
    }
  } ensuring(_ => time <= (k - i + 1) * 60)

  def kfibs(k: BigInt) = {
    require(k >= 1)
    fibRange(1, k)
  } ensuring(_ => time <= 70 * k)
}
