/* Copyright 2009-2016 EPFL, Lausanne */

package leon.synthesis

/*
 * This provides some algebra/number theory functions, including operation such as true division,
 * GCD and LCM as well as some matrix computation.
 *
 * Notice that all those functionalities are independent of the Leon language and
 * are working for Integer (by opposition to real numbers).
 */

object Algebra {
  /** Returns the remainder of the euclidian division between x an y (always positive) */
  def remainder(x: Int, y: Int) = ((x % y) + y.abs) % y.abs

  /** Returns the quotient of the euclidian division between a and b.*/
  def divide(a: Int, b: Int): (Int, Int) = {
    val r = remainder(a, b)
    ((a - r)/b, r)
  }

  /** Returns the remainder of the euclidian division between the big integers x an y (always positive) */
  def remainder(x: BigInt, y: BigInt) = ((x % y) + y.abs) % y.abs
  /** Returns the quotient of the euclidian division between the big integers x an y */
  def divide(a: BigInt, b: BigInt): (BigInt, BigInt) = {
    val r = remainder(a, b)
    ((a - r)/b, r)
  }
  /** Returns the gcd of two integers */
  def gcd(a: Int, b: Int): Int = {
    val (na, nb) = (a.abs, b.abs)
    def gcd0(a: Int, b: Int): Int = {
      require(a >= b)
      if(b == 0) a else gcd0(b, a % b)
    }
    if(na > nb) gcd0(na, nb) else gcd0(nb, na)
  }

  /** Returns the gcd of three or more integers */
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

  /** Returns the gcd of a non-empty sequence of integers */
  def gcd(as: Seq[Int]): Int = {
    require(as.length >= 1)
    if(as.length == 1)
      as.head.abs
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

  /** Returns the gcd of two big integers */
  def gcd(a: BigInt, b: BigInt): BigInt = {
    val (na, nb) = (a.abs, b.abs)
    def gcd0(a: BigInt, b: BigInt): BigInt = {
      require(a >= b)
      if(b == BigInt(0)) a else gcd0(b, a % b)
    }
    if(na > nb) gcd0(na, nb) else gcd0(nb, na)
  }

  /** Returns the gcd of three or more big integers  */
  def gcd(a1: BigInt, a2: BigInt, a3: BigInt, as: BigInt*): BigInt = {
    var tmp = gcd(a1, a2)
    tmp = gcd(tmp, a3)
    var i = 0
    while(i < as.size) {
      tmp = gcd(tmp, as(i))
      i += 1
    }
    tmp
  }

  /** Returns the gcd of a non-empty sequence of big integers */
  def gcd(as: Seq[BigInt]): BigInt = {
    require(as.length >= 1)
    if(as.length == 1)
      as.head.abs
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

  /** Returns the lcm of two integers */
  def lcm(a: Int, b: Int): Int = {
    val (na, nb) = (a.abs, b.abs)
    na*nb/gcd(a, b)
  }

  /** Returns the lcm of three or more integers */
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

  /** Returns the lcm of a sequence of integers */
  def lcm(as: Seq[Int]): Int = {
    require(as.length >= 1)
    if(as.length == 1)
      as.head.abs
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

  /** Returns the lcm of two big integers */
  def lcm(a: BigInt, b: BigInt): BigInt = {
    val (na, nb) = (a.abs, b.abs)
    na*nb/gcd(a, b)
  }

  /** Returns the lcm of three or more big integers */
  def lcm(a1: BigInt, a2: BigInt, a3: BigInt, as: BigInt*): BigInt = {
    var tmp = lcm(a1, a2)
    tmp = lcm(tmp, a3)
    var i = 0
    while(i < as.size) {
      tmp = lcm(tmp, as(i))
      i += 1
    }
    tmp
  }

  /** Returns the lcm of a sequence of big integers */
  def lcm(as: Seq[BigInt]): BigInt = {
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
  def extendedEuclid(a: BigInt, b: BigInt): (BigInt, BigInt) = {
    def rec(a: BigInt, b: BigInt): (BigInt, BigInt) = {
      require(a >= 0 && b >= 0)
      if(b == BigInt(0)) (1, 0) else {
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
    require(sol.length == equation.length)
    sol.zip(equation).foldLeft(0)((acc, p) => acc + p._1 * p._2)
  }

  //multiply the matrix by the vector: [M1 M2 .. Mn] * [v1 .. vn] = v1*M1 + ... + vn*Mn]
  def mult(matrix: Array[Array[Int]], vector: Array[Int]): Array[Int] = {
    require(vector.length == matrix(0).length && vector.length > 0)
    val tmat = matrix.transpose
    var tmp: Array[Int] = null
    tmp = mult(vector(0), tmat(0))
    var i = 1
    while(i < vector.length) {
      tmp = add(tmp, mult(vector(i), tmat(i)))
      i += 1
    }
    tmp
  }

  def mult(c: Int, v: Array[Int]): Array[Int] = v.map(_ * c)

  def add(v1: Array[Int], v2: Array[Int]): Array[Int] = {
    require(v1.length == v2.length)
    v1.zip(v2).map(p => p._1 + p._2)
  }

}
