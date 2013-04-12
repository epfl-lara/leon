import leon.Utils._

object SumAndMaxImp {

  def isPositive(a: Array[Int], size: Int): Boolean = {
    require(a.length >= 0 && size <= a.length)
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

  /* VSTTE 2010 challenge 1 */
  def maxSum(a: Array[Int]): (Int, Int) = {
    require(a.length >= 0 && isPositive(a, a.length))
    var sum = 0
    var max = 0
    var i = 0
    (while(i < a.length) {
      if(max < a(i)) 
        max = a(i)
      sum = sum + a(i)
      i = i + 1
    }) invariant (sum <= i * max && i >= 0 && i <= a.length)
    (sum, max)
  } ensuring(res => res._1 <= a.length * res._2)

}
