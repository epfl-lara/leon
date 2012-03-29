import leon.Utils._

object Bubble {

  def sort(a: Map[Int, Int], size: Int, k: Int): Map[Int, Int] = ({
    require(size > 0 && k < size - 1 && k >= 0)
    var i = size - 1
    var j = 0
    var sortedArray = a
    (while(i > 0) {
      j = 0
      (while(j < i) {
        if(sortedArray(j) > sortedArray(j+1)) {
          val tmp = sortedArray(j)
          sortedArray = sortedArray.updated(j, sortedArray(j+1))
          sortedArray = sortedArray.updated(j+1, tmp)
        }
        j = j + 1
      }) invariant(j >= 0 && j <= i)
      i = i - 1
    }) invariant(i >= 0 && i < size && (k < i || sortedArray(k) <= sortedArray(k+1)))
    sortedArray
  }) ensuring(res => res(k) <= res(k+1))
  //ensuring(res => sorted(res, 0, size-1))

  def sorted(a: Map[Int, Int], l: Int, u: Int): Boolean = {
    var k = l
    var sorted = true
    while(k < u) {
      if(a(k) > a(k+1))
        sorted = false
      k = k + 1
    }
    sorted
  }


  def isArray(a: Map[Int, Int], size: Int): Boolean = {
    def rec(i: Int): Boolean = if(i >= size) true else {
      if(a.isDefinedAt(i)) rec(i+1) else false
    }
    size > 0 && rec(0)
  }

}
