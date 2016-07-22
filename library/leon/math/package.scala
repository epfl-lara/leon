/* Copyright 2009-2016 EPFL, Lausanne */

package leon
import leon.annotation._
import leon.collection._

package object math {

  @library
  def min(i1: Int, i2: Int) = if (i1 <= i2) i1 else i2

  @library
  def max(i1: Int, i2: Int) = if (i1 >= i2) i1 else i2

  @library
  def min(i1: BigInt, i2: BigInt) = if (i1 <= i2) i1 else i2

  @library
  def max(i1: BigInt, i2: BigInt) = if (i1 >= i2) i1 else i2
  
  @library
  def abs(i: BigInt) = if(i < BigInt(0)) -i else i
  
  @library
  @annotation.isabelle.noBody()
  // Computes the vectorial product of two lists.
  def vectorialProduct(a: List[BigInt], b: List[BigInt]): BigInt = {
    require(a.length == b.length)
    a match {
      case Nil() => 0
      case Cons(ael, aq) => ael * b.head + vectorialProduct(aq, b.tail)
    }
  }
  
  @library
  @annotation.isabelle.noBody()
  def isGCDable(l: List[BigInt]): Boolean = l match {
    case Cons(x, b) if x == BigInt(0) => isGCDable(b)
    case Cons(x, b) => true
    case Nil() => false
  }
  
  /** Computes the GCD between numbers */
  @library
  @annotation.isabelle.noBody()
  def gcdlist(l:List[BigInt]):BigInt = {
    require(l.length > 0 && isGCDable(l))
    l match {
      case Cons(a, Nil()) => if(a < 0) -a else a
      case Cons(z, q) if z == BigInt(0) => gcdlist(q)
      case Cons(a, Cons(b, q)) => gcdlist(gcd(a,b)::q)
    }
  }
  
  /** Computes the LCM between numbers */
  @library
  @annotation.isabelle.noBody()
  def lcmlist(l:List[BigInt]):BigInt = {
    require(l.length > 0 && isGCDable(l))
    l match {
      case Cons(a, Nil()) => if(a < 0) -a else a
      case Cons(z, q) if z == BigInt(0) => lcmlist(q)
      case Cons(a, Cons(b, q)) => lcmlist(lcm(a,b)::q)
    }
  }
  
  /** Computes the GCD between two numbers */
  @library
  @annotation.isabelle.noBody()
  def gcd(x:BigInt, y:BigInt): BigInt = {
    require(x != 0 || y != 0)
    if (x==BigInt(0)) abs(y)
    else if (x<0) gcd(-x, y)
    else if (y<0) gcd(x, -y)
    else gcd(y%x, x)
  } ensuring { (res: BigInt) =>
    x % res == 0 && y % res == 0 && res > 0
  }
  
  /** Computes the LCM between two numbers */
  @library
  @annotation.isabelle.noBody()
  def lcm(x: BigInt, y: BigInt): BigInt = {
    require(x != 0 || y != 0)
    abs(x * y) / gcd(x, y)
  } ensuring { (res: BigInt) =>
    res % x == 0 && res % y == 0 && res > 0
  }
  
  /** Computes the GCD between two numbers. Axponential speed-up.*/
  /*@library
  def binaryGcd(a:BigInt, b:BigInt):BigInt = {
    var g = BigInt(1)
    var (u, v) = (a, b)
    while(u%2 == 0 && v%2 == 0) {
      u = u/2
      v = v/2
      g = 2*g
    }
    while(u != 0) {
      if(u % 2 == 0) u = u/2
      else if(v % 2 == 0) v = v/2
      else {
        val t = abs(u-v)/2
        if(u >= v) u = t else v = t
      }
    }
    g*v
  }*/
  
  /*@library
  def bezout(e: BigInt, a : List[BigInt]):List[BigInt] = {
    require(a.length > 0 && isGCDable(a))
    bezoutMM(a, e / gcdlist(a))
  }*/
  
  @library
  @annotation.isabelle.noBody()
  def bezoutWithBase(e: BigInt, a: List[BigInt]): (List[List[BigInt]]) = {
    require(isNonZero(a) && a.nonEmpty)
    bezoutWithBaseMMFunc(e, a)
  }
  
  /** Finds (x1, x2, k) such that x1.a + x2.b +  gcd(a,b) = 0 and k = gcd(a ,b) */
  /*@library
  def extendedEuclid(a_in: BigInt, b_in: BigInt):(BigInt, BigInt, BigInt) = {
    var (x, lastx) = (BigInt(0), BigInt(1))
    var (y, lasty) = (BigInt(1), BigInt(0))
    var (a, b) = (a_in, b_in)
    var (quotient, temp) = (BigInt(0), BigInt(0))
    while(b != 0) {
        val amodb = (abs(b) + a%b)%b
        quotient = (a - amodb)/b
        a = b
        b = amodb
        temp = x
        x = lastx-quotient*x
        lastx = temp
        temp = y
        y = lasty-quotient*y
        lasty = temp
    }
    if(a < 0)
      (lastx, lasty, -a)
    else
      (-lastx, -lasty, a)
  }*/
  
  // Finds coefficients x such that k*gcd(a_in) + x.a_in = 0
  /*@library
  def bezoutMM(a_in: List[BigInt], k: BigInt):List[BigInt] = {
    var a = a_in
    var a_in_gcds = a_in.foldRight(List[BigInt]()){
      case (i, Nil()) => List(i)
      case (i, a::q) => gcd(a, i)::a::q
    }
    var result:List[BigInt] = Nil()
    var last_coef = BigInt(-1)
    while(a.nonEmpty) {
      a match {
        case Cons(x, Nil()) if x == BigInt(0)  =>
          result = Cons(BigInt(0), result)
          a = Nil()
        case Cons(el, Nil()) =>
          // Solution is -el/abs(el)
          result = (k*(-last_coef * (-el/abs(el))))::result
          a = Nil()
        case Cons(el1, Cons(el2, Nil())) =>
          val (u, v, _) = extendedEuclid(el1, el2)
          result = (-v*k*last_coef)::(-u*k*last_coef)::result
          a = Nil()
        case (el1::q) =>
          val el2 = a_in_gcds.tail.head
          val (u, v, _) = extendedEuclid(el1, el2)
          result = (-u*k*last_coef)::result
          last_coef = -v*last_coef
          a = q
          a_in_gcds = a_in_gcds.tail
      }
    }
    result.reverse
  }*/
  
  // Finds coefficients x such that gcd(a_in) + x.a_in = 0
  /*@library
  def bezoutMM(a_in: List[BigInt]):List[BigInt] = bezoutMM(a_in, BigInt(1))*/

  /*@library
  def bezoutWithBaseMM(e: BigInt, a: List[BigInt]): (List[List[BigInt]]) = {
    var coefs = a
    var coefs_gcd = coefs.foldRight(List[BigInt]()){
      case (i, Nil()) => List(abs(i))
      case (i, Cons(a, q)) => gcd(a, i)::a::q
    }
    var n = a.length
    var result = List(bezoutMM(a, e/coefs_gcd.head)) // The gcd of all coefs divides e.
    var i = BigInt(1)
    var zeros:List[BigInt] = Nil()
    while(i <= n-BigInt(1)) {
      val kii = coefs_gcd.tail.head / coefs_gcd.head
      val kijs = bezoutMM(coefs.tail, coefs.head/coefs_gcd.head)
      result = Cons((zeros ++ Cons(kii, kijs)), result)
      coefs     = coefs.tail
      coefs_gcd = coefs_gcd.tail
      zeros     = Cons(BigInt(0), zeros)
      i += 1
    }
    result.reverse
  }*/
  
  @library
  @annotation.isabelle.noBody()
  def extendedEuclidFunc(a_in: BigInt, b_in: BigInt):(BigInt, BigInt, BigInt) = {
    require(a_in != 0 || b_in != 0)
    val (x, lastx) = (BigInt(0), BigInt(1))
    val (y, lasty) = (BigInt(1), BigInt(0))
    val (a, b) = (a_in, b_in)
    def aux(a: BigInt, b: BigInt, x: BigInt, y: BigInt, lastx: BigInt, lasty: BigInt): (BigInt, BigInt, BigInt) = {
      if (b == 0) {
        if(a < 0)
          (lastx, lasty, -a)
        else
          (-lastx, -lasty, a)
      } else {
        val amodb = (abs(b) + a%b)%b
        val quotient = (a - amodb)/b
        aux(b, amodb, lastx-quotient*x, lasty-quotient*y, x, y)
      }
    }
    aux(a, b, x, y, lastx, lasty)
  }/* ensuring { res =>
    val (x1, x2, k) = res
    x1 * a_in + x2 * b_in + k == 0 && k == gcd(a_in, b_in)
  }*/
  
  @library
  @annotation.isabelle.noBody()
  def isPositive(l: List[BigInt]): Boolean = l match {
    case Cons(a, b) => a > 0 && isPositive(b)
    case Nil() => true
  }
  @library
  @annotation.isabelle.noBody()
  def isNonZero(l: List[BigInt]): Boolean = l match {
    case Cons(a, b) => a != 0 && isNonZero(b)
    case Nil() => true
  }
  @library
  @annotation.isabelle.noBody()
  def foldRightGcds(es: List[BigInt]): List[BigInt] = {
    require(isNonZero(es))
    ((es match {
    case Cons(i, aq) => foldRightGcds(aq) match {
      case Cons(a, q) => gcd(a, i)::a::q
      case Nil() => List(abs(i))
    }
    case Nil() => Nil()
  }): List[BigInt])} ensuring {
    (res: List[BigInt]) =>
    isPositive(res) && res.length == es.length
  }
  
  @library
  @annotation.isabelle.noBody()
  def bezoutMMFunc(a_in: List[BigInt], k: BigInt):List[BigInt] = {
    require(isNonZero(a_in) && a_in.length > 0)
    val a = a_in
    
    val a_in_gcds = foldRightGcds(a_in)
    val result:List[BigInt] = Nil()
    val last_coef = BigInt(-1)
    def aux(a: List[BigInt], a_in_gcds: List[BigInt], result: List[BigInt], last_coef: BigInt): List[BigInt] = {
      require(isNonZero(a) && a_in_gcds == foldRightGcds(a))
      if(a.isEmpty) result.reverse
      else {
        a match {
        /*case Cons(x, Nil()) if x == BigInt(0)  =>
          aux(Nil(), a_in_gcds, Cons(BigInt(0), result), last_coef)*/
        case Cons(el, Nil()) =>
          // Solution is -el/abs(el)
          aux(Nil(), a_in_gcds, (k*(-last_coef * (-el/abs(el))))::result, last_coef)
        case Cons(el1, Cons(el2, Nil())) =>
          val (u, v, _) = extendedEuclidFunc(el1, el2)
          aux(Nil(), a_in_gcds, (-v*k*last_coef)::(-u*k*last_coef)::result, last_coef)
        case (el1::q) =>
          val el2 = a_in_gcds.tail.head
          val (u, v, _) = extendedEuclidFunc(el1, el2)
          aux(q, a_in_gcds.tail,  (-u*k*last_coef)::result, -v*last_coef)
        }
      }
    } ensuring {
      (res: List[BigInt]) => true
    }
    aux(a_in, a_in_gcds, result, last_coef)
  }/* ensuring {
    (x: List[BigInt]) =>
      vectorialProduct(x, a_in) + k*gcdlist(a_in) == 0
  }*/
  
  @library
  @annotation.isabelle.noBody()
  def bezoutWithBaseMMFunc(e: BigInt, a: List[BigInt]): (List[List[BigInt]]) = {
    require(isNonZero(a) && a.nonEmpty)
    val coefs = a
    val coefs_gcd = foldRightGcds(coefs)
    val n = a.length
    val result = List(bezoutMMFunc(a, e/coefs_gcd.head)) // The gcd of all coefs divides e.
    val i = BigInt(1)
    val zeros:List[BigInt] = Nil()
    def aux(i: BigInt, result: List[List[BigInt]], coefs: List[BigInt], coefs_gcd: List[BigInt], zeros: List[BigInt])
        : List[List[BigInt]] = {
      require(i <= n && coefs.length + i == a.length + BigInt(1) && isNonZero(coefs) && isPositive(coefs_gcd) && coefs_gcd == foldRightGcds(coefs) && (i == n || (coefs_gcd.length >= 2 && coefs.length >= 1)))
      if (i > n-BigInt(1)) {
        result.reverse
      } else {
        val kii = coefs_gcd.tail.head / coefs_gcd.head
        val kijs = bezoutMMFunc(coefs.tail, coefs.head/coefs_gcd.head)
        aux(i + 1, Cons((zeros ++ Cons(kii, kijs)), result), coefs.tail, coefs_gcd.tail, Cons(BigInt(0), zeros))
      }
    }
    aux(i, result, coefs, coefs_gcd, zeros)
  }
}

