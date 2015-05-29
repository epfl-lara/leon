import leon.lang._

object AbsArray {


  def abs(a: Array[BigInt]): Array[BigInt] = ({
    require(a.length > 0)
    var k = 0
    val res = Array.fill(a.length)(BigInt(0))
    (while(k < a.length) {
      if(a(k) < 0)
        res(k) = -a(k)
      else
        res(k) = a(k)
      k = k + 1
    }) invariant(
          k >= 0 && 
          k <= a.length && 
          a.length == res.length &&
          isPositive(res, k))
    res
  }) ensuring(res => isPositive(res, a.length))

  def isPositive(a: Array[BigInt], size: Int): Boolean = {
    require(a.length > 0 && size <= a.length)
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

}
