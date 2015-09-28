import leon.lang._

object Test {
  def focusCond(a: BigInt) = {
    a match {
      case BigInt(1) => (BigInt(2), BigInt(0))
      case BigInt(2) => (BigInt(2), BigInt(0))
      case _ => (BigInt(0), BigInt(0))
    }
  } ensuring {
    res => res._1 == a && res._2 > 1
  }
}
