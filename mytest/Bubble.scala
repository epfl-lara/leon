import leon.Utils._

object Bubble {

  def sort(a: Map[Int, Int], size: Int): Map[Int, Int] = {
    require(isArray(a, size))
    var i = size - 1
    var j = 0
    var sortedArray = a
    (while(i > 0) {
      j = 0
      (while(j < i) {
        if(a(j) > a(j+1)) {
          val tmp = sortedArray(j)
          sortedArray = sortedArray.updated(j, a(j+1))
          sortedArray = sortedArray.updated(j+1, tmp)
        }
        j = j + 1
      }) invariant(isArray(sortedArray, size) && j >= 0 && j <= i && i < size && i >= 0)
      i = i - 1
    }) invariant(isArray(sortedArray, size) && i >= 0 && i < size)
    sortedArray
  }


  def isArray(a: Map[Int, Int], size: Int): Boolean = {
    def rec(i: Int): Boolean = if(i >= size) true else {
      if(a.isDefinedAt(i)) rec(i+1) else false
    }
    size > 0 && rec(0)
  }

}
