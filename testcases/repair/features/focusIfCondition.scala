object Test {
  def focusCond(a: BigInt) = {
    if (a < 0) {
      -a + 1
    } else {
      a
    }
  } ensuring {
    _ > 0
  }
}
