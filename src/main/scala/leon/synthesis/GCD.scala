package leon.synthesis

object GCD {

  def remainder(x: Int, y: Int) = ((x % y) + y.abs) % y.abs

  def divide(a: Int, b: Int): (Int, Int) = {
    val r = remainder(a, b)
    ((a - r)/b, r)
  }

  def gcd(a: Int, b: Int): Int = {
    val (na, nb) = (a.abs, b.abs)
    def gcd0(a: Int, b: Int): Int = {
      require(a >= b)
      if(b == 0) a else gcd0(b, a % b)
    }
    if(na > nb) gcd0(na, nb) else gcd0(nb, na)
  }

  def gcd(a1: Int, a2: Int, a3: Int, as: Int*): Int = {
    var tmp = gcd(a1, a2)
    tmp = gcd(tmp, a3)
    var i = 0
    while(i < as.size) {
      tmp = gcd(tmp, as(i))
      i += 1
    }
    tmp
  }

  def gcd(as: Seq[Int]): Int = {
    require(as.length >= 1)
    if(as.length == 1)
      as(0).abs
    else {
      var tmp = gcd(as(0), as(1))
      var i = 2
      while(i < as.size) {
        tmp = gcd(tmp, as(i))
        i += 1
      }
      tmp
    }
  }

  //return (x, y) such that ax + by = gcd(a, b)
  def extendedEuclid(a: Int, b: Int): (Int, Int) = {
    def rec(a: Int, b: Int): (Int, Int) = {
      require(a >= 0 && b >= 0)
      if(b == 0) (1, 0) else {
        val (q, r) = divide(a, b)
        val (s, t) = extendedEuclid(b, r)
        (t, s - q * t)
      }
    }
    if(a >= 0 && b >= 0) rec(a, b)
    else if(a < 0 && b >= 0) {val (x, y) = rec(-a, b); (-x, y)}
    else if(a >= 0 && b < 0) {val (x, y) = rec(a, -b); (x, -y)}
    else if(a < 0 && b < 0) {val (x, y) = rec(-a, -b); (-x, -y)}
    else sys.error("shouldn't have forgot a case here")
  }

}
