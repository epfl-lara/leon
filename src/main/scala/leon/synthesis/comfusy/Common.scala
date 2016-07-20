package leon.synthesis.comfusy

object Common {
  
  sealed abstract class BezoutType
  case class OTBezout() extends BezoutType // Home-made
  case class MMBezout() extends BezoutType // Made manually.
  
  var computing_mode:BezoutType = MMBezout()

  def bezout(e: Int, a : List[Int]):List[Int] = {
    computing_mode match {
      case OTBezout() => bezoutOT(e, a)
      case MMBezout() => bezoutMM(a, e / gcdlist(a))
    }
  }
  def bezoutWithBase(e: Int, a: List[Int]): (List[List[Int]]) = {
    computing_mode match {
      case OTBezout() => bezoutWithBaseOT(e, a)
      case MMBezout() => bezoutWithBaseMM(e, a)
    }
  }

  /** Shortcuts */
  def bezout(e: Int, a : Int*): List[Int] = bezout(e, a.toList)
  def bezoutWithBase(e: Int, a : Int*): List[List[Int]] = bezoutWithBase(e, a.toList)
  
  /*
   * Algorithms derived from the Omega-tests
   */                                                                    
  
  // Finds a vector x such that x.a + e is 0 if this is possible.
  def bezoutOT(e: Int, a : List[Int]):List[Int] = {
    a match {
      case Nil => Nil
      case 0::Nil => 0::Nil
      case k::Nil => ((-e + smod(e, k))/k) :: Nil
      case a =>
        val a_indexed:List[(Int, Int)] = (a.indices zip a).toList
        (a_indexed find (_._2 == 0)) match {
          case Some((index, element)) =>
          // Takes the result when removing the zeros, then inserts some zeros.
            val a_filtered = a filterNot (_==0)
            val a_filtered_solved = bezoutOT(e, a_filtered )
            val (_, a_solved) = a.foldLeft((a_filtered_solved, Nil:List[Int]))((_,_) match { 
              case ((q, l), 0)    => (q, 0::l)
              case ((Nil, l), k)  => (Nil, l) // This should not happen, as we have many zeroes.
              case ((a::q, l), k) => (q, a::l)
            })
            a_solved.reverse
          case None =>
            (a_indexed find {case a => Math.abs(a._2) == 1}) match {
              case Some((index, element)) => // This is easy, like solving 4x+y+45z=30, just say that y=30 and other are zero
                val sign = if(element > 0) 1 else -1
                (a_indexed map { case (i, c) => if(i==index) -e/sign else 0 })
              case None =>
                    val (index, min_coef) = a_indexed reduceLeft {
                  (_, _) match {
                    case (t1@(i, ci), t2@(j, cj)) => if(Math.abs(ci) < Math.abs(cj)) t1 else t2
                  }}
                val min_coef_sign = if(min_coef > 0) 1 else -1
                val abs_min_coef_plus_1 = Math.abs(min_coef) + 1
                val e_assign = smod(e, abs_min_coef_plus_1)
                val a_assign = abs_min_coef_plus_1 :: (a map {case k => smod(k, abs_min_coef_plus_1)})
                // the coefficient at index 'index+1' is now 1 or -1.
                
                val new_e = (e + Math.abs(min_coef) * (smod(e, abs_min_coef_plus_1)))/abs_min_coef_plus_1
                val new_a = Math.abs(min_coef)::(a map {
                  case k => (k + Math.abs(min_coef) * (smod(k, abs_min_coef_plus_1)))/abs_min_coef_plus_1
                })
                // the coefficient at index 'index+1' is now 0, so it will be removed.
                
                // Now, there is at least one zero in new_a
                bezoutOT(new_e, new_a) match {
                  case Nil => throw new Error("Should not happen, the size of the input and output are the same")
                  case q@(w::l) =>
                    l.splitAt(index) match {
                    // The coefficient at index 'index' of l should be zero, we replace it by its assignment
                    case (left, 0::right) =>
                      val solution_a = scalarProduct(a_assign, q)
                      val solution = (solution_a + e_assign)*(min_coef_sign)
                      val result = left++(solution::right)
                      result
                    case (l, m) => throw new Error("The list "+l+" should have 0 at index "+index+" but this is not the case")
                  }
                }
            }
        }
    }
  }
  
  def enumerate[A](a: List[A]):List[(Int, A)] = (a.indices zip a).toList
  
  // a is an indexed list
  def replaceElementAtIndexByCoef(a: List[(Int, Int)], index: Int, coef: Int) = a map { _ match {
        case (i, c) =>  if(i == index) coef else c
    } }
  
  // a is an indexed list
  def replaceEverythingByCoef1ExceptCoef2AtIndex(a: List[(Int, Int)], coef1:Int, coef2: Int,index: Int): List[Int] =
    a map { _ match {
        case (i, c) if i == index => coef2
        case _ => coef1
      }
    }
  
  // a is an indexed list
  def replaceEverythingByZeroExcept1AtIndex(a: List[(Int, Int)], index: Int): List[Int] =
    replaceEverythingByCoef1ExceptCoef2AtIndex(a, 0, 1, index)

  // a is an indexed list
  def putCoef1AtIndex1andCoef2AtIndex2(a: List[(Int, Int)], coef1: Int, index1: Int, coef2: Int, index2: Int ):List[Int] = {
    a map { _ match {
        case (i, c) =>
          if(i == index1) coef1
          else if(i==index2) coef2
          else 0
      }
    }
  }
  
  //insertPreviousZeros([a, b, 0, c, 0, d], [x, y, z, w]) = [x, y, 0, z, 0, d]
  def insertPreviousZeros(list_with_zeros: List[Int], list_to_complete: List[Int]) :List[Int] = {
    val (_, result) = list_with_zeros.foldLeft((list_to_complete, Nil: List[Int]))( (_, _) match {
      case ((l, result), 0)    => (l, 0::result)
      case ((a::q, result), _) => (q, a::result)
    })
    result.reverse
  }
  
  def scalarProduct(a: List[Int], b:List[Int]): Int = {
    (a zip b).foldLeft(0){case (result, (e_a, e_b)) => result + e_a * e_b}
  }
  
  
  // If size(a) == n, finds a matrix x of size n x n
  // such that (1, k1, k2, .. kn-1).x.a + e = 0 if this is possible,
  // and x describes all integer solutions of this equation. Rank(x) = n-1
  // Output representation : it's the list of rows.
  //                               n          n     n
  def bezoutWithBaseOT(e: Int, a: List[Int]): (List[List[Int]]) = {
    a match {
      case Nil => Nil
      case 0::Nil => ((0::Nil)::Nil)
      case k::Nil => (((-e + smod(e, k))/k) :: Nil) :: Nil
      case a =>
        val a_indexed:List[(Int, Int)] = enumerate(a)
        (a_indexed find (_._2 == 0)) match {
          case Some((index, element)) =>
          // Takes the result when removing the zeros, then inserts some zeros.
            val a_filtered = a filterNot ( _ == 0 )
            val solution = bezoutWithBase(e, a_filtered)
            val (_, solution_completed) = a_indexed.foldLeft((solution, Nil:List[List[Int]]))((_,_) match { 
              case ((q, l), (i, 0))    => (q, replaceEverythingByZeroExcept1AtIndex(a_indexed, i)::l)
              case ((Nil, l), (i, k))  => (Nil, l) // This should not happen, as we have many zeroes.
              case ((b::q, l), (i, k)) => (q, insertPreviousZeros(a, b)::l)
            })
            // For each zero in a_indexed, add a new vector where 1 is at this position and it's zero everywhere else.
            val new_vectors = a_indexed flatMap {
              case (index, 0) => List(replaceEverythingByZeroExcept1AtIndex(a_indexed, index))
              case t => Nil
            }
            solution_completed.reverse
          case None =>
            (a_indexed find {case a => Math.abs(a._2) == 1}) match {
              case Some((index, element)) =>
                // This is easy, like solving 4x+y+45z=30, just say that y=30 and other are zero
                // For the vectors, just take the other variables as themselves.
                val neg_sign = if(element > 0) -1 else 1
                replaceEverythingByCoef1ExceptCoef2AtIndex(a_indexed, 0, neg_sign*e, index) ::
                (a_indexed flatMap ( _ match {
                  case (i, c) =>
                    if(i == index)
                      Nil
                    else
                      List(putCoef1AtIndex1andCoef2AtIndex2(a_indexed, 1, i, neg_sign*c, index))
                }))
              case None =>
                    val (index, min_coef) = a_indexed reduceLeft {
                  (_, _) match {
                    case (t1@(i, ci), t2@(j, cj)) => if(Math.abs(ci) < Math.abs(cj)) t1 else t2
                  }}
                val min_coef_sign = if(min_coef > 0) 1 else -1
                val min_coef_sign2 = if(min_coef > 0) -1 else 1
                val abs_min_coef_plus_1 = Math.abs(min_coef) + 1
                val e_assign = smod(e, abs_min_coef_plus_1)
                val a_assign = abs_min_coef_plus_1 :: (a map {case k => smod(k, abs_min_coef_plus_1)})
                // the coefficient at index 'index+1' is now 1 or -1.
                
                val new_e = (e + Math.abs(min_coef) * (smod(e, abs_min_coef_plus_1)))/abs_min_coef_plus_1
                val new_a = Math.abs(min_coef)::(a map {
                  case k => (k + Math.abs(min_coef) * (smod(k, abs_min_coef_plus_1)))/abs_min_coef_plus_1
                })
                // the coefficient at index 'index+1' is now 0, so it will be removed.
                
                // Now, there is at least one zero in new_a
                bezoutWithBase(new_e, new_a) match {
                  case Nil => throw new Error("Should not happen as the input was not empty")
                  case v =>
                    val v_reduced = enumerate(v) flatMap {
                      case (i, Nil) => throw new Error("Should not happen as the input was not empty")
                      case (i, vs@(a::q)) =>
                        if(i == index +1) // We drop the line indicated by index
                          Nil
                        else {
                          val vs_replaced = replaceElementAtIndexByCoef(enumerate(vs), index+1, 0)
                          if(i==0) {
                            val new_element = (e_assign+scalarProduct(a_assign, vs_replaced)) * min_coef_sign
                            List(replaceElementAtIndexByCoef(enumerate(q), index, new_element))
                          } else {
                            val new_element = (scalarProduct(a_assign, vs_replaced)) * min_coef_sign
                            List(replaceElementAtIndexByCoef(enumerate(q), index, new_element))
                          }
                        }
                    }
                    v_reduced
                }
            }
        }
    }
  }

  /*
   * Hand-made algorithms.
   */       
  
  // Finds (x1, x2, k) such that x1.a + x2.b +  gcd(a,b) = 0 and k = 
  // gcd(a ,b)
  def advancedEuclid(a_in: Int, b_in: Int):(Int, Int, Int) = {
    var (x, lastx) = (0, 1)
    var (y, lasty) = (1, 0)
    var (a, b) = (a_in, b_in)
    var (quotient, temp) = (0, 0)
    while(b != 0) {
        val amodb = (Math.abs(b) + a%b)%b
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
      return (lastx, lasty, -a)
    else
      return (-lastx, -lasty, a)
  }
  
  // Finds coefficients x such that k*gcd(a_in) + x.a_in = 0
  def bezoutMM(a_in: List[Int], k: Int):List[Int] = {
    var a = a_in
    var a_in_gcds = a_in.foldRight(Nil:List[Int]){
      case (i, Nil) => List(i)
      case (i, a::q) => gcd(a, i)::a::q
    }
    var result:List[Int] = Nil
    var last_coef = -1
    while(a != Nil) {
      a match {
        case Nil => 
        case 0::Nil  =>
          result = 0::result 
          a = Nil
        case el::Nil =>
          // Solution is -el/abs(el)
          result = (k*(-last_coef * (-el/Math.abs(el))))::result
          a = Nil
        case (el1::el2::Nil) =>
          val (u, v, _) = advancedEuclid(el1, el2)
          result = (-v*k*last_coef)::(-u*k*last_coef)::result
          a = Nil
        case (el1::q) =>
          val el2 = a_in_gcds.tail.head
          val (u, v, _) = advancedEuclid(el1, el2)
          result = (-u*k*last_coef)::result
          last_coef = -v*last_coef
          a = q
          a_in_gcds = a_in_gcds.tail
      }
    }
    result.reverse
  }
  
  // Finds coefficients x such that gcd(a_in) + x.a_in = 0
  def bezoutMM(a_in: List[Int]):List[Int] = bezoutMM(a_in, 1)

  
  def bezoutWithBaseMM(e: Int, a: List[Int]): (List[List[Int]]) = {
    var coefs = a
    var coefs_gcd = coefs.foldRight(Nil:List[Int]){
      case (i, Nil) => List(Math.abs(i))
      case (i, a::q) => gcd(a, i)::a::q
    }
    var n = a.length
    var result = List(bezoutMM(a, e/coefs_gcd.head)) // The gcd of all coefs divides e.
    var i = 1
    var zeros:List[Int] = Nil
    while(i <= n-1) {
      val kii = coefs_gcd.tail.head / coefs_gcd.head
      val kijs = bezoutMM(coefs.tail, coefs.head/coefs_gcd.head)
      result = (zeros ::: (kii :: kijs))::result
      coefs     = coefs.tail
      coefs_gcd = coefs_gcd.tail
      zeros     = 0::zeros
      i += 1
    }
    result.reverse
  }
  
  class MatrixIterator(val m: List[List[Int]]) {
    private var l:List[Int] = m.flatten 
    def next: Int = {
      val result = l.head
      l = l.tail
      result
    }
  }
  
  def smod(x:Int, m_signed:Int) = {
    val m = Math.abs(m_signed)
    val c = x % m
    if(c >= (m+1)/2)
      c - m
    else if(c < -m/2)
      c + m
    else c
  }
  
  // Computes the GCD between two numbers
  // Unsafe if y = -2^31
  def gcd(x:Int, y:Int): Int = {
    if (x==0) Math.abs(y)
    else if (x<0) gcd(-x, y)
    else if (y<0) gcd(x, -y)
    else gcd(y%x, x)
  }
  
  // Computes the GCD between two numbers. Binary speed-up.
  def binaryGcd(a:Int, b:Int):Int = {
    var g = 1
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
        val t = Math.abs(u-v)/2
        if(u >= v) u = t else v = t
      }
    }
    return g*v;
  }
  
  // Computes the LCM between two numbers
  def lcm(x: Int, y: Int): Int = {
    if(x < 0) lcm(-x, y)
    else if(y < 0) lcm(x, -y)
    else x * y / gcd(x, y)
  }
  // Computes the LCM over a list  of numbers
  // Do not handle correctly zero numbers.
  def lcmlist(l:List[Int]):Int = l match {
    case Nil => 1
    case 0::q => lcmlist(q)
    case a::Nil => if(a < 0) -a else a
    case (a::b::q) => lcmlist(lcm(a,b)::q)
  }
  // Computes the GCD over a list  of numbers
  // Do not handle zero numbers.
  def gcdlist(l:List[Int]):Int = l match {
    case Nil => throw new Exception("Cannot compute GCD of nothing")
    case 0::Nil => throw new Exception("Cannot compute GCD of zero")
    case a::Nil => if(a < 0) -a else a
    case (a::b::q) => gcdlist(gcd(a,b)::q)
  }
  // None represents infinity
  def gcdlistComplete(l:List[Int]):Option[Int] = l match {
    case Nil => None
    case 0::q => gcdlistComplete(q)
    case a::Nil => if(a < 0) Some(-a) else Some(a)
    case (a::b::q) => gcdlistComplete(gcd(a, b)::q) 
  }
}
