import leon.lang._

/* The calculus of Computation textbook */

object BubbleSort {

  def sort(a: Array[BigInt]): Unit = {
    require(a.length > 0)
    var i = a.length - 1
    var j = 0
    (while(i > 0) {
      j = 0
      (while(j < i) {
        if(a(j) > a(j+1)) {
          val tmp = a(j)
          a(j) = a(j+1)
          a(j+1) = tmp
        }
        j = j + 1
      }) invariant(
            j >= 0 &&
            j <= i &&
            i < a.length &&
            //partitioned(a, a.length, 0, i, i+1, size-1) &&
            //partitioned(a, size, 0, j-1, j, j) &&
            sorted(a, i, a.length-1)
          )
      i = i - 1
    }) invariant(
          i >= 0 &&
          i < a.length &&
          //partitioned(a, a.length, 0, i, i+1, a.length-1) &&
          sorted(a, i, a.length-1)
       )

  } ensuring(_ => sorted(a, 0, a.length-1))


  def sorted(a: Array[BigInt], l: Int, u: Int): Boolean = {
    require(a.length > 0 && l >= 0 && u < a.length && l <= u)
    boundedForall(l, u, (i: Int) => a(i) <= a(i+1))
  }

  def partitioned(a: Map[Int, Int], size: Int, l1: Int, u1: Int, l2: Int, u2: Int): Boolean = {
    require(l1 >= 0 && u1 < l2 && u2 < size /*&& isArray(a, size)*/ && size < 5)
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
