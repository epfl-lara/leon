import leon.Utils._

object Abs {


  def abs(tab: Map[Int, Int], size: Int, j: Int): Map[Int, Int] = {
    require(j >= 0 && j < size && tab.isDefinedAt(j) && size > 0)
    var k = 0
    var tabres = Map.empty[Int, Int]
    (while(k < size) {
      if(tab(k) < 0)
        tabres = tabres.updated(k, -tab(k))
      else
        tabres = tabres.updated(k, tab(k))
      k = k + 1
    }) invariant(k >= 0)
    tabres

  }

}
