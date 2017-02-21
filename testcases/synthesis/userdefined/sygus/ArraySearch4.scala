import leon.annotation._
import leon.lang._
import leon.lang.synthesis._
import leon.grammar._
import leon.annotation.grammar._

object Polynomial {
  
  @production(7)
  def v = variable[BigInt]
  
  @production(1)
  def c0 = BigInt(0)

  @production(1)
  def c1 = BigInt(1)

  @production(1)
  def c2 = BigInt(2)

  @production(1)
  def c3 = BigInt(3)

  @production(1)
  def c4 = BigInt(4)

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

  def findIdx(x1: BigInt, x2: BigInt, x3: BigInt, x4: BigInt, k: BigInt) = {
    require(x1 < x2 && x2 < x3 && x3 < x4)
    choose ( (res: BigInt) =>
      ((k < x1) ==> (res == 0)) &&
      ((k > x4) ==> (res == 4)) &&
      ((k > x1 && k < x2) ==> (res == 1)) &&
      ((k > x2 && k < x3) ==> (res == 2)) &&
      ((k > x3 && k < x4) ==> (res == 3))
    )
  }


}
