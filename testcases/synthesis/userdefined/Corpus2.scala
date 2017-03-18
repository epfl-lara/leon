package leon
package grammar

import leon.lang._
import leon.lang.synthesis._
import leon.collection._
import annotation.grammar._

object Grammar {

  //////////////////////////////////////////////////////////////////////////////
  // Boolean(10488)

  /* @production(51) // TODO! Confirm!
  def boolMatch(l: List[Int], v: Boolean, f: Int => List[Int] => Boolean) = l match {
    case Nil => v
    case Cons(hd, tl) => f(hd, tl)
  }
  @production(51) // TODO! Confirm!
  def boolMatch(l: List[BigInt], v: Boolean, f: Int => List[BigInt] => Boolean) = l match {
    case Nil => v
    case Cons(hd, tl) => f(hd, tl)
  } */

  @production(11)
  def contains(l: List[Int], v: Int) = l.contains(v)
  @production(11) // No observations in statistics. Introduced to allow possibility.
  def contains(l: List[BigInt], v: BigInt) = l.contains(v)

  @production(11) // No observations in statistics. Introduced to allow possibility.
  def contains(l: Set[Int], v: Int) = l.contains(v)
  @production(11) // No observations in statistics. Introduced to allow possibility.
  def contains(l: Set[BigInt], v: BigInt) = l.contains(v)

  @production(328)
  def equals(t1: BigInt, t2: BigInt) = t1 == t2
  @production(244)
  def equals(t1: Int, t2: Int) = t1 == t2
  @production(75)
  def equals(t1: Boolean, t2: Boolean) = t1 == t2
  @production(75) // TODO! Confirm!
  def equals(t1: Set[Int], t2: Set[Int]) = t1 == t2
  @production(24) // TODO! Confirm!
  def equals(t1: Set[BigInt], t2: Set[BigInt]) = t1 == t2
  @production(70) // TODO! Confirm!
  def equals(t1: List[BigInt], t2: List[BigInt]) = t1 == t2
  @production(70) // TODO! Confirm!
  def equals(t1: List[Int], t2: List[Int]) = t1 == t2

  @production(1062)
  def vrBoolean = variable[Boolean]

  @production(960)
  def and(b1: Boolean, b2: Boolean) = b1 && b2

  @production(395)
  def trueBool = true
  @production(214)
  def falseBool = false

  @production(411)
  def greaterEquals(i1: Int, i2: Int) = i1 >= i2
  @production(173)
  def greaterEquals(i1: BigInt, i2: BigInt) = i1 >= i2

  @production(458)
  def not(b: Boolean) = !b

  @production(332)
  def lessThan(i1: Int, i2: Int) = i1 < i2
  @production(98)
  def lessThan(i1: BigInt, i2: BigInt) = i1 < i2

  @production(183)
  def lessEquals(i1: Int, i2: Int) = i1 <= i2
  @production(119)
  def lessEquals(i1: BigInt, i2: BigInt) = i1 <= i2

  @production(257)
  def ifBool(b1: Boolean, b2: Boolean, b3: Boolean) = if (b1) b2 else b3

  @production(113)
  def greaterThanInt(i1: Int, i2: Int) = i1 > i2
  @production(109)
  def greaterThanBigInt(i1: BigInt, i2: BigInt) = i1 > i2

  @production(124)
  def or(b1: Boolean, b2: Boolean) = b1 || b2

  @production(46)
  def implies(b1: Boolean, b2: Boolean) = b1 ==> b2

  @production(3)
  def subsetOf(e1: Set[Int], e2: Set[Int]) = e1.subsetOf(e2)
  @production(3) // No observations in statistics. Introduced to allow possibility.
  def subsetOf(e1: Set[BigInt], e2: Set[BigInt]) = e1.subsetOf(e2)

  //////////////////////////////////////////////////////////////////////////////
  // Int(7023)

  /* @production(13) // TODO! Confirm!
  def intMatch(l: List[Int], v: Int, f: Int => List[Int] => Int) = l match {
    case Nil => v
    case Cons(hd, tl) => f(hd, tl)
  }
  @production(13) // No observations in statistics. Introduced to allow possibility.
  def intMatch(l: List[BigInt], v: BigInt, f: BigInt => List[BigInt] => Int) = l match {
    case Nil => v
    case Cons(hd, tl) => f(hd, tl)
  } */

  @production(63) // TODO! Confirm!
  def listSize(l: List[Int]) = l.size
  @production(63) // TODO! Confirm!
  def listSize(l: List[BigInt]) = l.size

  @production(3460)
  def vrInt = variable[Int]

  @production(658)
  def zeroInt: Int = 0
  @production(387)
  def oneInt: Int = 1
  @production(87)
  def twoInt: Int = 2
  @production(25)
  def threeInt: Int = 3
  @production(46)
  def minusOneInt: Int = -1

  @production(304)
  def bvplus(i1: Int, i2: Int) = i1 + i2

  @production(101)
  def bvminus(i1: Int, i2: Int) = i1 - i2

  @production(41)
  def ifInt(b: Boolean, i1: Int, i2: Int) = if (b) i1 else i2

  @production(20)
  def times(i1: Int, i2: Int) = i1 * i2

  @production(10)
  def bvashiftright(i1: Int, i2: Int) = i1 >> i2

  @production(6)
  def bvand(i1: Int, i2: Int) = i1 & i2

  @production(5)
  def bvxor(i1: Int, i2: Int) = i1 ^ i2

  @production(4)
  def bvshiftleft(i1: Int, i2: Int) = i1 << i2

  @production(3)
  def bvlshiftright(i1: Int, i2: Int) = i1 >>> i2

  @production(3)
  def bvor(i1: Int, i2: Int) = i1 | i2

  @production(2)
  def bvrem(i1: Int, i2: Int) = i1 % i2

  @production(1)
  def bvuminus(i: Int) = -i

  //////////////////////////////////////////////////////////////////////////////
  // BigInt(5283)
  
  @production(2445)
  def vrBigInt = variable[BigInt]

  @production(479)
  def zeroigInt = BigInt(0)
  @production(325)
  def oneBigInt = BigInt(1)
  @production(94)
  def twoBigInt = BigInt(2)
  @production(6)
  def minusOneBigInt = BigInt(-1)

  // TODO! Function Invocations!
  // TODO! Matches

  @production(245)
  def minus(v1: BigInt, v2: BigInt) = v1 - v2
  @production(187)
  def plus(v1: BigInt, v2: BigInt) = v1 + v2
  @production(116)
  def times(v1: BigInt, v2: BigInt) = v1 * v2
  @production(46)
  def ifBigInt(cond: Boolean, v1: BigInt, v2: BigInt) = if (cond) v1 else v2
  @production(32)
  def division(v1: BigInt, v2: BigInt) = v1 / v2
  @production(18)
  def rem(v1: BigInt, v2: BigInt) = v1 % v2

  //////////////////////////////////////////////////////////////////////////////
  // Set[Int]

  // TODO! Function invocation(287)
  // TODO! Literals
  // TODO! Match

  @production(287)
  def setUnionInt(s1: Set[Int], s2: Set[Int]) = s1 ++ s2
  @production(44)
  def vrSetInt = variable[Set[Int]]
  @production(1)
  def setIfInt(cond: Boolean, s1: Set[Int], s2: Set[Int]) = if (cond) s1 else s2
  @production(1)
  def setDiffInt(s1: Set[Int], s2: Set[Int]) = s1 -- s2

  //////////////////////////////////////////////////////////////////////////////
  // Set[BigInt]

  // TODO! Function invocation(76)
  // TODO! Literals
  // TODO! Match

  @production(28)
  def setUnionBigInt(s1: Set[BigInt], s2: Set[BigInt]) = s1 ++ s2
  @production(16)
  def vrSetBigInt = variable[Set[BigInt]]
  @production(2)
  def setAddBigInt(s1: Set[BigInt], v: BigInt) = s1 + v
  @production(1)
  def setDiffBigInt(s1: Set[BigInt], s2: Set[BigInt]) = s1 -- s2
  @production(1)
  def setIntersectionBigInt(s1: Set[BigInt], s2: Set[BigInt]) = s1 & s2

  //////////////////////////////////////////////////////////////////////////////
  // List[Int]
  // TODO! Recompute these numbers! They are the same as those for List[BigInt]!

  @production(50)
  def vrListInt = variable[List[Int]]
  // TODO! Function invocation
  @production(1)
  def ifListInt(cond: Boolean, l1: List[Int], l2: List[Int]) = if (cond) l1 else l2
  @production(1)
  def matchListInt(l1: List[Int], l2: List[Int], f: (Int, List[Int]) => List[Int]) = l1 match {
    case Nil() => l2
    case Cons(hd, tl) => f(hd, tl)
  }

  //////////////////////////////////////////////////////////////////////////////
  // List[BigInt](73)

  @production(50)
  def vrListBigInt = variable[List[BigInt]]
  // TODO! Function invocation
  @production(1)
  def ifListBigInt(cond: Boolean, l1: List[BigInt], l2: List[BigInt]) = if (cond) l1 else l2
  @production(1)
  def matchListBigInt(l1: List[BigInt], l2: List[BigInt], f: (BigInt, List[BigInt]) => List[BigInt]) = l1 match {
    case Nil() => l2
    case Cons(hd, tl) => f(hd, tl)
  }

}
