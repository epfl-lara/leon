package eagerEval

import leon._
import annotation._
import invariant._
import instrumentation._

object BigNums {
  sealed abstract class Digit
  case class Zero() extends Digit {
    @ignore 
    override def toString = "0"
  }
  case class One() extends Digit {
    @ignore 
    override def toString = "1"
  }
  
  sealed abstract class BigNum
  case class Cons(head: Digit, tail: BigNum) extends BigNum
  case class Nil() extends BigNum

  /**
   * Time taken by the increment method
   * The number of leading one's
   */
  def leadingOnes(l: BigNum) : BigInt = {
    l match {
      case Nil() => 1
      case Cons(Zero(), tail) => 1
      case Cons(_, tail) => 1 + leadingOnes(tail)
    }
  }

  /**
   * Total number of one's in the number
   */
  def numOnes(l: BigNum) : BigInt = {
    l match {
      case Nil() => 0
      case Cons(Zero(), tail) => numOnes(tail)
      case Cons(_, tail) => 1 + numOnes(tail)
    }
  }
  
  /**
   * Increments a number
   */
  def increment(l: BigNum) : BigNum = {
    l match {
      case Nil()              => Cons(One(), l)
      case Cons(Zero(), tail) => Cons(One(), tail)
      case Cons(_, tail) => 
        Cons(Zero(), increment(tail))
    }
  } ensuring (res => time <= ? * leadingOnes(l) + ? && leadingOnes(l) + numOnes(res) - numOnes(l) <= ?)
  
  def firstDigit(l: BigNum): Digit = {
    require(l != Nil())
    l match {
      case Cons(d, _) => d
    }
  }

  /**
   * Nop is the number of operations
   */
  def incrUntil(nop: BigInt, l: BigNum) : BigNum = {
    if(nop == 0)  l
    else {
      incrUntil(nop-1, increment(l))
    }
  } ensuring (res => time <= ? * nop + ? * numOnes(l) + ?)

  def count(nop: BigInt) : BigNum = {
    incrUntil(nop, Nil())
  } ensuring (res => time <= ? * nop + ?)

}
