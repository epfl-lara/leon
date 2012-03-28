import leon.Utils._

object Abs {


  def abs(tab: Map[Int, Int], size: Int, j: Int): Map[Int, Int] = ({
    require(j >= 0 && j < size)
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
    def rec(i: Int): Boolean = if(i >= size) true else {
      if(a.isDefinedAt(i)) rec(i+1) else false
    }
    size > 0 && rec(0)
  }

}
