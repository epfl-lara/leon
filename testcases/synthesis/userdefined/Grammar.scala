package leon
package grammar

import leon.lang.synthesis._
import annotation.grammar._

object Grammar {

  // BIGINT
  @terminal
  @weight(68)
  def vr = variable[BigInt]

  @terminal
  @weight(122)
  def zero = BigInt(0)

  @terminal
  @weight(2)
  def one = BigInt(1)

  @production
  @weight(12)
  def plus(b1: BigInt, b2: BigInt) = b1 + b2

  @production
  @weight(2)
  def minus(b1: BigInt, b2: BigInt) = b1 - b2

  @production
  @weight(4)
  def ite(cond: Boolean, thenn: BigInt, elze: BigInt) = {
    if(cond) thenn else elze
  }

  // BOOLEAN

  @production
  @weight(4)
  def smaller(b1: BigInt, b2: BigInt) = b1 < b2

  @production
  @weight(5)
  def and(b1: Boolean, b2: Boolean) = b1 && b2

  @production
  @weight(1)
  def or(b1: Boolean, b2: Boolean) = b1 || b2

  @terminal
  @weight(10)
  def t = true

  def min(b1: BigInt, b2: BigInt) = choose( (out: BigInt) => {
    out >= b1 && out >= b2 && (out == b1 || out == b2)
  })
}

