import leon.Utils._

object Bubble {

  def sort(a: Map[Int, Int], size: Int, k: Int, l1: Int, l2: Int): Map[Int, Int] = ({
    require(size <= 5 && size > 0 && k < size - 1 && k >= 0 && l1 < size && l1 >= 0 && l2 < size && l2 >= 0 && isArray(a, size))
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
      }) invariant(
            isArray(sortedArray, size) && 
            j >= 0 && 
            j <= i &&
            (if(k >= i) sortedArray(k) <= sortedArray(k+1) else true) && 
            (if(l1 <= i && l2 > i) sortedArray(l1) <= sortedArray(l2) else true)
          )
      i = i - 1
    }) invariant(
          isArray(sortedArray, size) && 
          i >= 0 && 
          i < size && 
          (if(k >= i) sortedArray(k) <= sortedArray(k+1) else true) && 
          (if(l1 <= i && l2 > i) sortedArray(l1) <= sortedArray(l2) else true)
       )
    sortedArray
  }) ensuring(res => res(k) <= res(k+1))
  //ensuring(res => sorted(res, 0, size-1))

  //def sorted(a: Map[Int, Int], l: Int, u: Int): Boolean = {
  //  require(isArray(a, u+1))
  //  var k = l
  //  var isSorted = true
  //  while(k < u) {
  //    if(a(k) > a(k+1))
  //      isSorted = false
  //    k = k + 1
  //  }
  //  isSorted
  //}


  def isArray(a: Map[Int, Int], size: Int): Boolean = {
    def rec(i: Int): Boolean = if(i >= size) true else {
      if(a.isDefinedAt(i)) rec(i+1) else false
    }
    size > 0 && rec(0)
  }

}
