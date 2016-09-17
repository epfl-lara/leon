package withOrb

import leon._
import mem._
import lang._
import annotation._
import instrumentation._
import invariant._

object FibMem {
  sealed abstract class IList
  case class Cons(x: BigInt, tail: IList) extends IList
  case class Nil() extends IList

  @memoize
  def fibRec(n: BigInt): BigInt = {
    require(n >= 0)
    if (n <= 2)
      BigInt(1)
    else
      fibRec(n - 1) + fibRec(n - 2) 
  } ensuring (res => res <= 0 && steps <= ? * n + ?)
    // postcondition is an invalid property
}
