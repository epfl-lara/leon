object Test {
  def focusCond(a: BigInt) = {
    val tmp = -a
    tmp
  } ensuring {
    _ > 0
  }
}
