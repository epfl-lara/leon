
object Test {
  def f(x: BigInt): BigInt = {
    if (x == 0) {
      0
    } else if (x > 0) {
      f(x-1)+2
    } else if (x < 0) {
      f(x+1)-2
    } else {
      33
    }
  } ensuring (_ == x*2)
}
