import leon.lang._
import leon.collection._
import leon._

object DivisionByZero {

  def divByZero(x: BigInt): Boolean = {
    (x / BigInt(0) == BigInt(10))
  }

}
