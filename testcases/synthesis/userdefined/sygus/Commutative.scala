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

  def comm(x: BigInt, y: BigInt): BigInt = ???[BigInt] ensuring { _ == comm(y, x) }
}
