import leon.lang._

/* VSTTE 2008 - Dafny paper */

object BinarySearch {

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


  def sorted(a: Array[Int], l: Int, u: Int) : Boolean = {
    require(a.length >= 0 && l >= 0 && l <= u && u < a.length)
    val t = sortedWhile(true, l, l, u, a)
    t._1
  }

  def sortedWhile(isSorted: Boolean, k: Int, l: Int, u: Int, a: Array[Int]): (Boolean, Int) = {
    require(a.length >= 0 && l >= 0 && l <= u && u < a.length && k >= l && k <= u)
    if(k < u) {
      sortedWhile(if(a(k) > a(k + 1)) false else isSorted, k + 1, l, u, a)
    } else (isSorted, k)
  }
}
