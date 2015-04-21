import leon.lang._

object ArrayOperations {

  /* VSTTE 2008 - Dafny paper */
  def binarySearch(a: Array[Int], key: Int): Int = ({
    require(a.length > 0 && sorted(a, 0, a.length - 1))
    var low = 0
    var high = a.length - 1
    var res = -1

    (while(low <= high && res == -1) {
      val i = (high + low) / 2
      val v = a(i)

      if(v == key)
        res = i

      if(v > key)
        high = i - 1
      else if(v < key)
        low = i + 1
    }) invariant(
        res >= -1 &&
        res < a.length &&
        0 <= low && 
        low <= high + 1 && 
        high >= -1 &&
        high < a.length && 
        (if (res >= 0) 
            a(res) == key else 
            (!occurs(a, 0, low, key) && !occurs(a, high + 1, a.length, key))
        )
       )
    res
  }) ensuring(res => 
      res >= -1 && 
      res < a.length && 
      (if(res >= 0) a(res) == key else !occurs(a, 0, a.length, key)))


  def occurs(a: Array[Int], from: Int, to: Int, key: Int): Boolean = {
    require(a.length >= 0 && to <= a.length && from >= 0)
    def rec(i: Int): Boolean = {
      require(i >= 0)
      if(i >= to) 
        false 
      else {
       if(a(i) == key) true else rec(i+1)
      }
    }
    if(from >= to)
      false
    else
      rec(from)
  }

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

  /* The calculus of Computation textbook */
  def bubbleSort(a: Array[Int]): Array[Int] = ({
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

  /* The calculus of Computation textbook */
  def linearSearch(a: Array[Int], c: Int): Boolean = ({
    require(a.length >= 0)
    var i = 0
    var found = false
    (while(i < a.length) {
      if(a(i) == c)
        found = true
      i = i + 1
    }) invariant(
         i <= a.length && 
         i >= 0 && 
         (if(found) contains(a, i, c) else !contains(a, i, c))
       )
    found
  }) ensuring(res => if(res) contains(a, a.length, c) else !contains(a, a.length, c))

  def contains(a: Array[Int], size: Int, c: Int): Boolean = {
    require(a.length >= 0 && size >= 0 && size <= a.length)
    content(a, size).contains(c)
  }
  
  def content(a: Array[Int], size: Int): Set[Int] = {
    require(a.length >= 0 && size >= 0 && size <= a.length)
    var set = Set.empty[Int]
    var i = 0
    (while(i < size) {
      set = set ++ Set(a(i))
      i = i + 1
    }) invariant(i >= 0 && i <= size)
    set
  }

  def abs(tab: Array[Int]): Array[Int] = ({
    require(tab.length >= 0)
    var k = 0
    val tabres = Array.fill(tab.length)(0)
    (while(k < tab.length) {
      if(tab(k) < 0)
        tabres(k) = -tab(k)
      else
        tabres(k) = tab(k)
      k = k + 1
    }) invariant(
        tabres.length == tab.length && 
        k >= 0 && k <= tab.length && 
        isPositive(tabres, k))
    tabres
  }) ensuring(res => isPositive(res, res.length))

  def isPositive(a: Array[Int], size: Int): Boolean = {
    require(a.length >= 0 && size <= a.length)
    def rec(i: Int): Boolean = {
      require(i >= 0)
      if(i >= size) 
        true 
      else {
        if(a(i) < 0) 
          false 
        else 
          rec(i+1)
      }
    }
    rec(0)
  }

  /* VSTTE 2010 challenge 1 */
  def maxSum(a: Array[Int]): (Int, Int) = ({
    require(a.length >= 0 && isPositive(a, a.length))
    var sum = 0
    var max = 0
    var i = 0
    (while(i < a.length) {
      if(max < a(i)) 
        max = a(i)
      sum = sum + a(i)
      i = i + 1
    }) invariant (sum <= i * max && i >= 0 && i <= a.length)
    (sum, max)
  }) ensuring(res => res._1 <= a.length * res._2)

}
