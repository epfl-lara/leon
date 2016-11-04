package leon
package grammar

import leon.lang.synthesis._
import annotation.grammar._

object Grammar {

  // BIGINT
  @production(68)
  def vr = variable[BigInt]

  @production(122)
  @tag("0")
  def zero = BigInt(0)

  @production
  @tag("1")
  def one = BigInt(1)
/*
  @production(12)
  @tag("plus")
  def plus(b1: BigInt, b2: BigInt) = b1 + b2

  @production(2)
  @tag("minus")
  def minus(b1: BigInt, b2: BigInt) = b1 - b2

  @production(4)
  def ite(cond: Boolean, thenn: BigInt, elze: BigInt) = {
    if(cond) thenn else elze
  }
*/
  // BOOLEAN

  @production(4)
  def smaller(b1: BigInt, b2: BigInt) = b1 < b2
/*
  @production(5)
  def and(b1: Boolean, b2: Boolean) = b1 && b2

  @production(1)
  def or(b1: Boolean, b2: Boolean) = b1 || b2

  //@production(10)
  //def t = true
*/
  def min(b1: BigInt, b2: BigInt) = choose( (out: BigInt) => {
    out >= b1 && out >= b2 && (out == b1 || out == b2)
  })
}

