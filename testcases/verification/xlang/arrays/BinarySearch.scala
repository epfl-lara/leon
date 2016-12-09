import leon.lang._

/* VSTTE 2008 - Dafny paper */

object BinarySearch {

  def fullBinarySearch(a: Array[BigInt], key: BigInt): Int = ({
    require(a.length > 0 && isSorted(a, 0, a.length - 1))

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
        0 <= low && 0 <= high && low <= high + 1 && high < a.length &&
        (if(res == -1)
          arrayForall(a, 0, low, (el: BigInt) => el != key) && 
          arrayForall(a, high+1, a.length, (el: BigInt) => el != key)
        else
          res >= 0 && res < a.length &&
          a(res) == key)
        )
    res
  }) ensuring(res => {
      if(res == -1)
        arrayForall(a, (el: BigInt) => el != key)
      else
        a(res) == key
     })

  //def isSorted(a: Array[BigInt], l: Int, u: Int): Boolean = {
  //  require(a.length > 0 && l >= 0 && u < a.length && l <= u)
  //  boundedForall(l, u, (i: Int) => a(i) <= a(i+1))
  //}

  def mid(a: Int, b: Int, t: Array[BigInt]): BigInt = {
    require(a >= 0 && a - 1 <= b && b < t.length && a <= b && (t.length == 0 || isSorted(t, 0, t.length-1)))
    val index = (b + a)/2
    t(index)
  }

  def binarySearch(a: Array[BigInt], key: BigInt): Int = ({
    require(a.length == 0 || isSorted(a, 0, a.length - 1))

    var low = 0
    var high = a.length - 1
    var res = -1

    (while(low <= high && res == -1) {
      val i = low + (high - low)/2 //no overflow here, if using (low+high)/2, it timeouts
      val v = a(i)

      if(v == key)
        res = i

      if(v > key)
        high = i - 1
      else if(v < key)
        low = i + 1
    }) invariant(
        0 <= low && low - 1 <= high && high < a.length && res >= -1 && res < a.length &&
        ((res != -1) ==> (a(res) == key))
       )
    res
  }) ensuring(res => (res != -1) ==> (a(res) == key))

  def isSorted(a: Array[BigInt], l: Int, u: Int): Boolean = {
    require(l >= 0 && u < a.length && l <= u)
    if(l == u) true else a(l) <= a(l+1) && isSorted(a, l+1, u)
  }

}
