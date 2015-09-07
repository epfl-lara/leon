import leon.lang._
import leon.lang.synthesis._


object Sort {
  def plusone(a: BigInt): BigInt = {
    choose((x: BigInt) => x > a)
  }
}
