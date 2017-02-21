import leon.annotation._
import leon.lang._
import leon.lang.synthesis._
import leon.grammar._
import leon.annotation.grammar._

object Polynomial {
  
  @production(4)
  def v = variable[BigInt]
  
  @production(1)
  def zero = BigInt(0)

  @production(1)
  def one = BigInt(1)

  @production(1)
  def two = BigInt(2)

  @production(1)
  def three = BigInt(3)

  @production(1)
  def ite(c: Boolean, t: BigInt, e: BigInt) = if (c) t else e

  @production(1)
  def lt(x: BigInt, y: BigInt) = x < y

  @production(1)
  def le(x: BigInt, y: BigInt) = x <= y

  @production(1)
  def gt(x: BigInt, y: BigInt) = x > y

  @production(1)
  def ge(x: BigInt, y: BigInt) = x >= y

  def findIdx(x1: BigInt, x2: BigInt, x3: BigInt, k: BigInt) = {
    require(x1 < x2 && x2 < x3)
    choose ( (res: BigInt) =>
      ((k < x1) ==> (res == 0)) &&
      ((k > x3) ==> (res == 3)) &&
      ((k > x1 && k < x2) ==> (res == 1)) &&
      ((k > x2 && k < x3) ==> (res == 2))
    )
  }


}
