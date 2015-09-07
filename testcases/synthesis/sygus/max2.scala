import leon.lang._
import leon.lang.synthesis._


object Sort {
  def max2(a: BigInt, b: BigInt): BigInt = {
    choose((x: BigInt) => x >= a && x >= b && (x == a || x == b))
  }
}
