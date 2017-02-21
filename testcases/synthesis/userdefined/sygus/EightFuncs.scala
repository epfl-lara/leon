import leon.annotation._
import leon.lang._
import leon.lang.synthesis._
import leon.grammar._
import leon.annotation.grammar._

object Commutative {
  
  @production(2)
  def v = variable[BigInt]
  
  @production(1)
  def plus(x: BigInt, y: BigInt) = x + y
  
  @production(1)
  def minus(x: BigInt, y: BigInt) = x - y

  @production(1)
  def tuple8(
    t1: BigInt, t2: BigInt, t3: BigInt, t4: BigInt,
    t5: BigInt, t6: BigInt, t7: BigInt, t8: BigInt
  ) = (t1, t2, t3, t4, t5, t6, t7, t8)

  def funcs(x: BigInt, y: BigInt): (BigInt, BigInt, BigInt, BigInt, BigInt, BigInt, BigInt, BigInt) = 
    choose {(t: (BigInt, BigInt, BigInt, BigInt, BigInt, BigInt, BigInt, BigInt) ) =>
    val ( f1, f2, f3, f4, f5, g1, g2, g3) = t
    f2 == f1 + f1 &&
    f3 == f1 + f2 - y &&
    f2 == f2 + f2 &&
    f5 == f4 + f1 &&
    g1 == f1 - y &&
    g2 == g1 + 1 &&
    g3 == g2 + 1
  }
}
