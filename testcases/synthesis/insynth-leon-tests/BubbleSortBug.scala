import leon.lang._

/* The calculus of Computation textbook */

object BubbleSortBug {

  def sort(a: Array[Int]): Array[Int] = ({
    require(a.length >= 1)
    var i = a.length - 1
    var j = 0
    val sa = a.clone
    (while(i > 0) {
      j = 0
      (while(j < i) {
        if(sa(j) < sa(j+1)) {
          val tmp = sa(j)
          sa(j) = sa(j+1)
          
          hole(0)
          
          sa(j+1) = tmp
        }
        j = j + 1
      }) invariant(j >= 0 && j <= i && i < sa.length)
      i = i - 1
    }) invariant(i >= 0 && i < sa.length)
    sa
  }) ensuring(res => true)

}
