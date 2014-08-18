import leon.lang._

object AbsArray {


  def abs(tab: Map[Int, Int], size: Int): Map[Int, Int] = ({
    require(size <= 5 && isArray(tab, size))
    var k = 0
    var tabres = Map.empty[Int, Int]
    (while(k < size) {
      if(tab(k) < 0)
        tabres = tabres.updated(k, -tab(k))
      else
        tabres = tabres.updated(k, tab(k))
      k = k + 1
    }) invariant(isArray(tabres, k) && k >= 0 && k <= size && isPositive(tabres, k))
    tabres
  }) ensuring(res => isArray(res, size) && isPositive(res, size))

  def isPositive(a: Map[Int, Int], size: Int): Boolean = {
    require(size <= 10 && isArray(a, size))
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
