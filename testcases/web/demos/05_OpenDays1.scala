import leon.lang._
import leon.lang.synthesis._
import leon.annotation._

object EpflOpenDays {

  def max3(a: BigInt, b: BigInt, c: BigInt): BigInt = {
    if (a > b) {
      if (c > a) {
        c
      } else {
        a
      }
    } else {
      if (c > b) {
        c
      } else {
        a
      }
    }
  } ensuring {
    res => res >= a && res >= b && res >= c
  }
}
