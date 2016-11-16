package leon
package grammar

import leon.lang.synthesis._
import annotation.grammar._

object Grammar {

  // BIGINT
  @production(68)
  def vr = variable[BigInt]

  @production(12)
  @tag("0")
  def zero = BigInt(0)

  @production
  @tag("1")
  def one = BigInt(1)

  @production(1)
  @tag("plus")
  def plus(b1: BigInt, b2: BigInt) = b1 + b2

  @production(1)
  @tag("minus")
  def minus(b1: BigInt, b2: BigInt) = b1 - b2

  @production(21)
  def ite(cond: Boolean, thenn: BigInt, elze: BigInt) = {
    if(cond) thenn else elze
  }

  // BOOLEAN

  @production(17)
  def smaller(b1: BigInt, b2: BigInt) = b1 < b2

  @production(10)
  def and(b1: Boolean, b2: Boolean) = b1 && b2

  @production(8)
  def or(b1: Boolean, b2: Boolean) = b1 || b2

  @production(20)
  def t = true

  def max(b1: BigInt, b2: BigInt, b3: BigInt) = choose( (out: BigInt) => {
    out >= b1 && out >= b2 && out >= b3 && (out == b1 || out == b2 || out == b3)
  })
}

