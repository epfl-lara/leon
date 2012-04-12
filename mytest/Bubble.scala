import leon.Utils._

/* The calculus of Computation textbook */

object Bubble {

  def sort(a: Map[Int, Int], size: Int): Map[Int, Int] = ({
    require(size <= 5 && isArray(a, size))
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
            j >= 0 &&
            j <= i &&
            i < size &&
            isArray(sortedArray, size) && 
            partitioned(sortedArray, size, 0, i, i+1, size-1) &&
            partitioned(sortedArray, size, 0, j-1, j, j) &&
            sorted(sortedArray, size, i, size-1)
          )
      i = i - 1
    }) invariant(
          i >= -1 &&
          i < size &&
          isArray(sortedArray, size) && 
          partitioned(sortedArray, size, 0, i, i+1, size-1) &&
          sorted(sortedArray, size, i, size-1)
       )
    sortedArray
  }) ensuring(res => sorted(res, size, 0, size-1))

  def sorted(a: Map[Int, Int], size: Int, l: Int, u: Int): Boolean = {
    require(isArray(a, size) && size < 5 && l >= 0 && u < size && l <= u)
    var k = l
    var isSorted = true
    (while(k < u) {
      if(a(k) > a(k+1))
        isSorted = false
      k = k + 1
    }) invariant(k <= u && k >= l)
    isSorted
  }
  
  def partitioned(a: Map[Int, Int], size: Int, l1: Int, u1: Int, l2: Int, u2: Int): Boolean = {
    require(l1 >= 0 && l1 <= u1 && u1 < l2 && l2 <= u2 && u2 < size && isArray(a, size) && size < 5)
    var i = l1
    var j = l2
    var isPartitionned = true
    (while(i <= u1) {
      j = l2
      (while(j <= u2) {
        if(a(i) > a(j))
          isPartitionned = false
        j = j + 1
      }) invariant(j >= l2 && i <= u1)
      i = i + 1
    }) invariant(i >= l1)
    isPartitionned
  }

  def isArray(a: Map[Int, Int], size: Int): Boolean = {
    def rec(i: Int): Boolean = if(i >= size) true else {
      if(a.isDefinedAt(i)) rec(i+1) else false
    }
    if(size < 0)
      false
    else
      rec(0)
  }

}
