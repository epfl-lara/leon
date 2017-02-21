import leon.annotation._
import leon.lang._
import leon.lang.synthesis._
import leon.grammar._
import leon.annotation.grammar._

object QmLoop {
  
  @production(1)
  def v = variable[BigInt]
  
  @production(1)
  def one = BigInt(1)

  @production(1)
  def zero = BigInt(0)

  @production(1)
  def three = BigInt(3)

  @production(1)
  def plus(x: BigInt, y: BigInt) = x + y
  
  @production(1)
  def minus(x: BigInt, y: BigInt) = x - y

  @production(1)
  def qmProd(x: BigInt, y: BigInt) = qm(x, y)

  def qm(x: BigInt, y: BigInt) = if (x < 0) y else x

  def qmLoop(x: BigInt): BigInt = ???[BigInt] ensuring { _ == (if (x <= 0) BigInt(3) else x - 1) }
}
