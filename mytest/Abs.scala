import leon.Utils._

object Abs {


  def abs(tab: Map[Int, Int], size: Int, j: Int): Map[Int, Int] = ({
    require(size <= 5 && /*)
    require(*/isArray(tab, size) && j >= 0 && j < size)
    var k = 0
    var tabres = Map.empty[Int, Int]
    (while(k < size) {
      if(tab(k) < 0)
        tabres = tabres.updated(k, -tab(k))
      else
        tabres = tabres.updated(k, tab(k))
      k = k + 1
    }) invariant(k >= 0 && k <= size && (if(j < k) tabres(j) >= 0 else true))
    tabres
  }) ensuring(res => res(j) >= 0)

  def isArray(a: Map[Int, Int], size: Int): Boolean = {
    if(size < 0)
      false
    else
      rec(a, size, 0)
  }

  def rec(a: Map[Int, Int], size: Int, i: Int): Boolean = {
    require(i >= 0 && i <= size)
    if(i >= size) true else { 
      if(a.isDefinedAt(i)) rec(a, size, i+1) else false
    }
  }

}
