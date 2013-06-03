/* Copyright 2009-2013 EPFL, Lausanne */

package leon.synthesis

/*
 * This provides some algebra/number theory functions, including operation such as true division,
 * GCD and LCM as well as some matrix computation.
 *
 * Notice that all those functionalities are independent of the Leon language and
 * are working for Integer (by opposition to real numbers).
 */

object Algebra {

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

  def lcm(a: Int, b: Int): Int = {
    val (na, nb) = (a.abs, b.abs)
    na*nb/gcd(a, b)
  }

  def lcm(a1: Int, a2: Int, a3: Int, as: Int*): Int = {
    var tmp = lcm(a1, a2)
    tmp = lcm(tmp, a3)
    var i = 0
    while(i < as.size) {
      tmp = lcm(tmp, as(i))
      i += 1
    }
    tmp
  }

  def lcm(as: Seq[Int]): Int = {
    require(as.length >= 1)
    if(as.length == 1)
      as(0).abs
    else {
      var tmp = lcm(as(0), as(1))
      var i = 2
      while(i < as.size) {
        tmp = lcm(tmp, as(i))
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


  //val that the sol vector with the term in the equation
  def eval(sol: Array[Int], equation: Array[Int]): Int = {
    require(sol.size == equation.size)
    sol.zip(equation).foldLeft(0)((acc, p) => acc + p._1 * p._2)
  }

  //multiply the matrix by the vector: [M1 M2 .. Mn] * [v1 .. vn] = v1*M1 + ... + vn*Mn]
  def mult(matrix: Array[Array[Int]], vector: Array[Int]): Array[Int] = {
    require(vector.size == matrix(0).size && vector.size > 0)
    val tmat = matrix.transpose
    var tmp: Array[Int] = null
    tmp = mult(vector(0), tmat(0))
    var i = 1
    while(i < vector.size) {
      tmp = add(tmp, mult(vector(i), tmat(i)))
      i += 1
    }
    tmp
  }

  def mult(c: Int, v: Array[Int]): Array[Int] = v.map(_ * c)

  def add(v1: Array[Int], v2: Array[Int]): Array[Int] = {
    require(v1.size == v2.size)
    v1.zip(v2).map(p => p._1 + p._2)
  }

}
