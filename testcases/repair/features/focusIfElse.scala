object Test {
  def focusCond(a: BigInt) = {
    if (a > 0) {
      a
    } else {
      BigInt(-1)
    }
  } ensuring {
    _ > 0
  }
}
