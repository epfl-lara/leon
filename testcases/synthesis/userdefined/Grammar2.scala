package leon
package grammar

import leon.lang._
import leon.lang.synthesis._
import annotation.grammar._

object Grammar {

  // BIGINT
  @production(1)
  def vr = variable[BigInt]

  @production(1)
  @tag("0")
  def zero = BigInt(0)

  @production(1)
  @tag("1")
  def one = BigInt(1)

  @production(1)
  @tag("plus")
  def plus(b1: BigInt, b2: BigInt) = b1 + b2

  @production(1)
  @tag("minus")
  def minus(b1: BigInt, b2: BigInt) = b1 - b2

  @production(1)
  def ite(cond: Boolean, thenn: BigInt, elze: BigInt) = {
    if(cond) thenn else elze
  }

  // BOOLEAN

  @production(1)
  def smaller(b1: BigInt, b2: BigInt) = b1 < b2

  @production(1)
  def and(b1: Boolean, b2: Boolean) = b1 && b2

  @production(1)
  def or(b1: Boolean, b2: Boolean) = b1 || b2

  @production(1)
  def t = true

  /* def max(b1: BigInt, b2: BigInt, b3: BigInt) = choose( (out: BigInt) => {
    out >= b1 && out >= b2 && out >= b3 && (out == b1 || out == b2 || out == b3)
  }) */

  def add1(b1: BigInt, b2: BigInt) = {
    ???[BigInt]
    // choose ((res: BigInt) => res >= b1 && res >= b2)
  } ensuring {
    res => ((b1, b2), res) passes {
      case (BigInt(3), BigInt(4)) => BigInt(7)
      case (BigInt(4), BigInt(7)) => BigInt(11)
    }
  }

}

