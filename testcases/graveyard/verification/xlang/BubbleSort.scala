import leon.lang._

/* The calculus of Computation textbook */

object BubbleSort {

  def sort(a: Array[Int]): Array[Int] = ({
    require(a.length >= 1)
    var i = a.length - 1
    var j = 0
    val sa = a.clone
    (while(i > 0) {
      j = 0
      (while(j < i) {
        if(sa(j) > sa(j+1)) {
          val tmp = sa(j)
          sa(j) = sa(j+1)
          sa(j+1) = tmp
        }
        j = j + 1
      }) invariant(
            j >= 0 &&
            j <= i &&
            i < sa.length &&
            sa.length >= 0 &&
            partitioned(sa, 0, i, i+1, sa.length-1) &&
            sorted(sa, i, sa.length-1) &&
            partitioned(sa, 0, j-1, j, j)
          )
      i = i - 1
    }) invariant(
          i >= 0 &&
          i < sa.length &&
          sa.length >= 0 &&
          partitioned(sa, 0, i, i+1, sa.length-1) &&
          sorted(sa, i, sa.length-1)
       )
    sa
  }) ensuring(res => sorted(res, 0, a.length-1))

  def sorted(a: Array[Int], l: Int, u: Int): Boolean = {
    require(a.length >= 0 && l >= 0 && u < a.length && l <= u)
    var k = l
    var isSorted = true
    (while(k < u) {
      if(a(k) > a(k+1))
        isSorted = false
      k = k + 1
    }) invariant(k <= u && k >= l)
    isSorted
  }

  def partitioned(a: Array[Int], l1: Int, u1: Int, l2: Int, u2: Int): Boolean = {
    require(a.length >= 0 && l1 >= 0 && u1 < l2 && u2 < a.length)
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
