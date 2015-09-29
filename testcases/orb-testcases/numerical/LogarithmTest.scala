import leon.invariant._
import leon.annotation._

object LogarithmTest {

  @monotonic
  def log(x: BigInt) : BigInt = {
    require(x >= 0)
    if(x <= 1) BigInt(0)
    else {
      1 + log(x/2)
    }
  } ensuring(_ >= 0)

  def binarySearchAbs(x: BigInt, min: BigInt, max: BigInt): BigInt = {
    require(max - min >= 0)
    if (max - min <= 1) BigInt(2)
    else {
      val mid = (min + max) / 2
      if (x < mid) {
        binarySearchAbs(x, min, mid) + 5
      } else if (x > mid) {
        binarySearchAbs(x, mid + 1, max) + 7
      } else
        BigInt(8)
    }
  } ensuring(res => tmpl((a,b) => res <= a*log(max - min) + b))
  //ensuring(res => tmpl((a,b) => res <= 7*log(max - min) + 2))
  //
}
