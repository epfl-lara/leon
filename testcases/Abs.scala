import leon.Utils._

object Abs {


  def abs(tab: Array[Int]): Array[Int] = ({
    require(tab.length >= 0)
    var k = 0
    val tabres = Array.fill(tab.length)(0)
    (while(k < tab.length) {
      if(tab(k) < 0)
        tabres(k) = -tab(k)
      else
        tabres(k) = tab(k)
      k = k + 1
    }) invariant(
        tabres.length == tab.length && 
        k >= 0 && k <= tab.length && 
        isPositive(tabres, k))
    tabres
  }) ensuring(res => isPositive(res, res.length))

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

}
