import leon.Utils._

object Abs {


  def abs(tab: Map[Int, Int], size: Int, j: Int): Map[Int, Int] = ({
    require(j >= 0 && j < size && size > 0)
    var k = 0
    var tabres = Map.empty[Int, Int]
    (while(k < size) {
      if(tab.isDefinedAt(k)) {
        if(tab(k) < 0)
          tabres = tabres.updated(k, -tab(k))
        else
          tabres = tabres.updated(k, tab(k))
      } else {
        tabres = tabres.updated(k, 0)
      }
      k = k + 1
    }) invariant(k >= 0 && (if(j < k) tabres(j) >= 0 else true))
    tabres
  }) ensuring(res => res(j) >= 0)

}
