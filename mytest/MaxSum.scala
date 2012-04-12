import leon.Utils._

/* VSTTE 2010 challenge 1 */

object MaxSum {


  def maxSum(a: Map[Int, Int], size: Int): (Int, Int) = ({
    require(isArray(a, size) && size < 5 && isPositive(a, size))
    var sum = 0
    var max = 0
    var i = 0
    (while(i < size) {
      if(max < a(i)) 
        max = a(i)
      sum = sum + a(i)
      i = i + 1
    }) invariant (sum <= i * max && /*isGreaterEq(a, i, max) &&*/ /*(if(i == 0) max == 0 else true) &&*/ i >= 0 && i <= size)
    (sum, max)
  }) ensuring(res => res._1 <= size * res._2)

/*
  def isGreaterEq(a: Map[Int, Int], size: Int, n: Int): Boolean = {
    require(size <= 5 && isArray(a, size))
    def rec(i: Int): Boolean = {
      require(i >= 0)
      if(i >= size) 
        true 
      else {
        if(a(i) > n) 
          false 
        else 
          rec(i+1)
      }
    }
    rec(0)
  }
  */

  def isPositive(a: Map[Int, Int], size: Int): Boolean = {
    require(size <= 5 && isArray(a, size))
    def rec(i: Int): Boolean = {
      require(i >= 0)
      if(i >= size) 
        true 
      else {
        if(a(i) < 0) 
          false 
        else 
          rec(i+1)
      }
    }
    rec(0)
  }

  def isArray(a: Map[Int, Int], size: Int): Boolean = {

    def rec(i: Int): Boolean = {
      require(i >= 0)  
      if(i >= size) true else {
        if(a.isDefinedAt(i)) rec(i+1) else false
      }
    }

    if(size < 0)
      false
    else
      rec(0)
  }
}
