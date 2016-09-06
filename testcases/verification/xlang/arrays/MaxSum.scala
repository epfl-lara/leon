import leon.lang._

/* VSTTE 2010 challenge 1 */

object MaxSum {

  //not valid because of Int, unfortunately conversion between big int and
  //int does not work and we cannot compute a.length * Max (Int * BigInt)
  def maxSum(a: Array[Int]): (Int, Int) = {
    require(a.length >= 0)
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
