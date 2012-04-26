import leon.Utils._

/* VSTTE 2008 - Dafny paper */

object BinarySearch {

  def binarySearch(a: Map[Int, Int], size: Int, key: Int): Int = ({
    require(isArray(a, size) && size < 5 && sorted(a, size, 0, size - 1))
    var low = 0
    var high = size - 1
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
    }) invariant(0 <= low && low <= high + 1 && high < size && (if(res >= 0) a(res) == key else (!occurs(a, 0, low, key) && !occurs(a, high + 1, size, key))))
    res
  }) ensuring(res => res >= -1 && res < size && (if(res >= 0) a(res) == key else !occurs(a, 0, size, key)))


  def occurs(a: Map[Int, Int], from: Int, to: Int, key: Int): Boolean = {
    require(isArray(a, to) && to < 5 && from >= 0)
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


  def isArray(a: Map[Int, Int], size: Int): Boolean = {

    def rec(i: Int): Boolean = {
      require(i >= 0)  
      if(i >= size) true else {
        if(a.isDefinedAt(i)) rec(i+1) else false
      }
    }

    if(size < 0)
      false
    else
      rec(0)
  }

  def sorted(a: Map[Int,Int], size: Int, l: Int, u: Int) : Boolean = {
    require(isArray(a, size) && size < 5 && l >= 0 && l <= u && u < size)
    val t = sortedWhile(true, l, l, u, a, size)
    t._1
  }

  def sortedWhile(isSorted: Boolean, k: Int, l: Int, u: Int, a: Map[Int,Int], size: Int) : (Boolean, Int) = {
    require(isArray(a, size) && size < 5 && l >= 0 && l <= u && u < size && k >= l && k <= u)
    if(k < u) {
      sortedWhile(if(a(k) > a(k + 1)) false else isSorted, k + 1, l, u, a, size)
    } else (isSorted, k)
  }
}
