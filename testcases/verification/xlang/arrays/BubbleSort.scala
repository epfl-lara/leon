import leon.lang._

/* The calculus of Computation textbook */

object BubbleSort {

  def sort(a: Array[BigInt]): Array[BigInt] = {
    require(a.length > 0)
    var i = a.length - 1
    var j = 0
    var sortedArray: Array[BigInt] = a
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
            partitioned(sortedArray, size, 0, i, i+1, size-1) &&
            //partitioned(sortedArray, size, 0, j-1, j, j) &&
            sorted(sortedArray, size, i, size-1)
          )
      i = i - 1
    }) invariant(
          i >= 0 &&
          i < size &&
          isArray(sortedArray, size) && 
          partitioned(sortedArray, size, 0, i, i+1, size-1) &&
          sorted(sortedArray, size, i, size-1)
       )
    sortedArray
  }) ensuring(res => sorted(res, size, 0, size-1))


  def sorted(a: Array[Int], l: Int, u: Int): Boolean = {
    require(a.length > 0 && l >= 0 && u < a.length && l <= u)
    boundedForall(l, u, (i: Int) => a(i) <= a(i+1))
  }

  def partitioned(a: Map[Int, Int], size: Int, l1: Int, u1: Int, l2: Int, u2: Int): Boolean = {
    require(l1 >= 0 && u1 < l2 && u2 < size && isArray(a, size) && size < 5)
    if(l2 > u2 || l1 > u1)
      true
    else {
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
  }
}
