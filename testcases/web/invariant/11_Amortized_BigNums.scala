import leon.invariant._
import leon.instrumentation._

object BigNums {
  sealed abstract class BigNum
  case class Cons(head: BigInt, tail: BigNum) extends BigNum
  case class Nil() extends BigNum

  def incrTime(l: BigNum) : BigInt = {
    l match {
      case Nil() => 1
      case Cons(x, tail) =>
        if(x == 0) 1
        else 1 + incrTime(tail)
    }
  }

  def potentialIncr(l: BigNum) : BigInt = {
    l match {
      case Nil() => 0
      case Cons(x, tail) =>
        if(x == 0) potentialIncr(tail)
        else 1 + potentialIncr(tail)
    }
  }

  def increment(l: BigNum) : BigNum = {
    l match {
      case Nil() => Cons(1,l)
      case Cons(x, tail) =>
        if(x == 0) Cons(1, tail)
        else Cons(0, increment(tail))
    }
  } ensuring (res => time <= ? * incrTime(l) + ? && incrTime(l) + potentialIncr(res) - potentialIncr(l) <= ?)

  /**
   * Nop is the number of operations
   */
  def incrUntil(nop: BigInt, l: BigNum) : BigNum = {
    if(nop == 0)  l
    else {
      incrUntil(nop-1, increment(l))
    }
  } ensuring (res => time <= ? * nop + ? * potentialIncr(l) + ?)

  def count(nop: BigInt) : BigNum = {
    incrUntil(nop, Nil())
  } ensuring (res => time <= ? * nop + ?)

}
