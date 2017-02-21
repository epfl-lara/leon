import leon.annotation._
import leon.lang._
import leon.lang.synthesis._
import leon.grammar._
import leon.annotation.grammar._

object Polynomial {
  
  @production(2)
  def v = variable[BigInt]
  
  @production(1)
  def plus(x: BigInt, y: BigInt) = x + y

  /*
  @production(1)
  def zero = BigInt(0)

  @production(1)
  def one = BigInt(1)
  */

  @production(1)
  def minus(x: BigInt, y: BigInt) = x - y

  @production(1)
  def pair(x: BigInt, y: BigInt) = (x, y)

  def synth1(x: BigInt, y: BigInt) = choose ( (r1: BigInt, r2: BigInt) =>
    r1 + r2 == x + y
  )


}
