package leon
package grammar

import leon.lang.synthesis._
import annotation.grammar._
import Grammar._

object Grammar {
  @terminal
  @weight(10)
  def zero = BigInt(0)

  @production
  @weight(10)
  def plus(b1: BigInt, b2: BigInt) = b1 + b2

  @production
  @weight(5)
  def minus(b1: BigInt, b2: BigInt) = b1 - b2

  @production
  @weight(4)
  def smaller(b1: BigInt, b2: BigInt) = b1 < b2

  @production
  @weight(4)
  def ite(cond: Boolean, thenn: BigInt, elze: BigInt) = {
    if(cond) thenn else elze
  }

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
    val x = minus(1,2)
    out >= b1 && out >= b2 && (out == b1 || out == b2)
  })
}

