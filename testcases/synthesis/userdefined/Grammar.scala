package leon
package grammar

import leon.lang._
import leon.lang.synthesis._
import annotation.grammar._


object Grammar {

  // BIGINT
  @production(68)
  def vr = variable[BigInt]

  @production(12)
  @tag("0")
  def zero = BigInt(0)

  @production(1)
  @tag("1")
  def one = BigInt(1)

  @production(1)
  @tag("plus")
  def plus(b1: BigInt, b2: BigInt) = b1 + b2

  @production(2)
  @tag("minus")
  def minus(b1: BigInt, b2: BigInt) = b1 - b2

  @production(40)
  @tag("ite")
  def ite(cond: Boolean, thenn: BigInt, elze: BigInt) = {
    if(cond) thenn else elze
  }

  // INT
  @production(68)
  def vrI = variable[Int]

  @production(12)
  @tag("0")
  def zeroI = 0

  @production(1)
  @tag("1")
  def oneI = 1

  @production(1)
  @tag("plus")
  def plusI(i1: Int, i2: Int) = i1 + i2

  @production(2)
  @tag("minus")
  def minusI(i1: Int, i2: Int) = i1 - i2

  @production(40)
  @tag("ite")
  def iteI(cond: Boolean, thenn: Int, elze: Int) = {
    if(cond) thenn else elze
  }

  // BOOLEAN
  @production(41)
  def smaller(b1: BigInt, b2: BigInt) = b1 < b2

  @production(41)
  def smallerI(i1: Int, i2: Int) = i1 < i2

  @production(5)
  @tag("and")
  def and(b1: Boolean, b2: Boolean) = b1 && b2

  @production(1)
  @tag("or")
  def or(b1: Boolean, b2: Boolean) = b1 || b2

  @production(1)
  @tag("booleanC")
  def t = true

  // SPECIFICATIONS
  def max3(b1: BigInt, b2: BigInt, b3: BigInt) = choose( (out: BigInt) => {
    out >= b1 && out >= b2 && out >= b3 && (out == b1 || out == b2 || out == b3)
  })

  def max3Ex(b1: BigInt, b2: BigInt, b3: BigInt) = {
    ???[BigInt]
  } ensuring {
    res => ((b1, b2, b3), res) passes {
      case (BigInt(3), BigInt(4), BigInt(9)) => BigInt(9)
      case (BigInt(4), BigInt(7), BigInt(1)) => BigInt(7)
      case (BigInt(4), BigInt(2), BigInt(1)) => BigInt(4)
      case (BigInt(10), BigInt(5), BigInt(50)) => BigInt(50)
      case (BigInt(100), BigInt(5), BigInt(50)) => BigInt(100)
      case (BigInt(10), BigInt(30), BigInt(20)) => BigInt(30)
    }
  }

  def max4Ex(b1: BigInt, b2: BigInt, b3: BigInt, b4: BigInt) = {
    ???[BigInt]
  } ensuring {
    res => (((b1, b2, b3, b4), res) passes {
      case (BigInt(1), BigInt(2), BigInt(3), BigInt(4)) => BigInt(4)
      case (BigInt(1), BigInt(2), BigInt(4), BigInt(3)) => BigInt(4)
      case (BigInt(1), BigInt(4), BigInt(2), BigInt(3)) => BigInt(4)
      case (BigInt(4), BigInt(1), BigInt(2), BigInt(3)) => BigInt(4)
    }) // && res >= b1 && res >= b2 && res >= b3 && res >= b4
  }

  def max3ExInt(b1: Int, b2: Int, b3: Int) = {
    ???[Int]
  } ensuring {
    res => (((b1, b2, b3), res) passes {
      case (1, 2, 3) => 3
      case (1, 3, 2) => 3
      case (3, 1, 2) => 3
    }) && res >= b1 && res >= b2 && res >= b3
  }

  def add1Ex(b: BigInt) = {
    ???[BigInt]
  } ensuring {
    res => (b, res) passes {
      case BigInt(3) => BigInt(4)
      case BigInt(4) => BigInt(5)
    }
  }

  def add2Ex(b1: BigInt, b2: BigInt) = {
    ???[BigInt]
  } ensuring {
    res => ((b1, b2), res) passes {
      case (BigInt(3), BigInt(4)) => BigInt(7)
      case (BigInt(4), BigInt(7)) => BigInt(11)
    }
  }

  def funny(b1: BigInt, b2: BigInt) = {
    choose ((res: BigInt) => res >= b1 && res >= b2)
  } ensuring {
    res => ((b1, b2), res) passes {
      case (BigInt(3), BigInt(4)) => BigInt(7)
      case (BigInt(4), BigInt(7)) => BigInt(11)
    }
  }

}
