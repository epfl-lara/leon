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
  def tuple5(t1: BigInt, t2: BigInt, t3: BigInt, t4: BigInt, t5: BigInt) = (t1, t2, t3, t4, t5)

  // We get a solution (0, 0, -y, 0, 0) which looks right but too easy,
  // and not the one suggested in the solutions
  def funcs(x: BigInt, y: BigInt): (BigInt, BigInt, BigInt, BigInt, BigInt) = 
    choose (( f1: BigInt, f2: BigInt, f3: BigInt, f4: BigInt, f5: BigInt) =>
    f2 == f1 + f1 &&
    f3 == f1 + f2 - y &&
    f2 == f2 + f2 &&
    f5 == f4 + f1
  )
}
