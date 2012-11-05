package leon.synthesis

object GCD {

  def divide(a: Int, b: Int): (Int, Int) = (a / b, a % b)

  def gcd(a: Int, b: Int): Int = {
    def gcd0(a: Int, b: Int): Int = {
      require(a >= b)
      if(b == 0) a else gcd0(b, a % b)
    }
    if(a > b) gcd0(a, b) else gcd0(b, a)
  }

  //return (x, y) such that ax + by = gcd(a, b)
  def extendedEuclid(a: Int, b: Int): (Int, Int) = if(b == 0) (1, 0) else {
    val (q, r) = divide(a, b)
    val (s, t) = extendedEuclid(b, r)
    (t, s - q * t)
  }

}
