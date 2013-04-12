import leon.Utils._

object BinarySearchFun {

  def binarySearch(a: Array[Int], key: Int, low: Int, high: Int): Int = ({
    require(a.length > 0 && sorted(a, low, high) &&
        0 <= low && low <= high + 1 && high < a.length
    )

    if(low <= high) {
      val i = (high + low) / 2
      val v = a(i)

      if(v == key) i
      else if (v > key) binarySearch(a, key, low, i - 1)
      else binarySearch(a, key, i + 1, high)
    } else -1
  }) ensuring(res =>
      res >= -1 &&
      res < a.length &&
      (if (res >= 0)
          a(res) == key else
          (high < 0 || (!occurs(a, low, (high+low)/2, key) && !occurs(a, (high+low)/2, high, key)))
      )
    )


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
    require(a.length >= 0 && l >= 0 && l <= u + 1 && u < a.length)
    val t = sortedWhile(true, l, l, u, a)
    t._1
  }

  def sortedWhile(isSorted: Boolean, k: Int, l: Int, u: Int, a: Array[Int]): (Boolean, Int) = {
    require(a.length >= 0 && l >= 0 && l <= u+1 && u < a.length && k >= l && k <= u + 1)
    if(k < u) {
      sortedWhile(if(a(k) > a(k + 1)) false else isSorted, k + 1, l, u, a)
    } else (isSorted, k)
  }
}

// vim: set ts=4 sw=4 et:
