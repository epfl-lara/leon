import leon.lang._

object Test {
  def focusMatch(a: BigInt, b: BigInt) = {
    (a, b) match {
      case (otherA, BigInt(0)) => otherA
      case _ => a+1
    }
  } ensuring {
    res => if (b == 0) {
      res == 0
    } else {
      res == a+1
    }
  }
}
