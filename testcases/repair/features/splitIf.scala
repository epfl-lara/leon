object Test {
  def focusCond(a: BigInt) = {
    if (a <= 0) {
      (a, BigInt(0))
    } else {
      (a, BigInt(0))
    }
  } ensuring {
    res => res._1 == a && res._2 > 1
  }
}
