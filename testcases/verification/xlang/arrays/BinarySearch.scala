import leon.lang._

/* VSTTE 2008 - Dafny paper */

object BinarySearch {

  def binarySearch(a: Array[BigInt], key: BigInt): Int = ({
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

  def isSorted(a: Array[BigInt], l: Int, u: Int): Boolean = {
    require(a.length > 0 && l >= 0 && u < a.length && l <= u)
    boundedForall(l, u, (i: Int) => a(i) <= a(i+1))
  }

}
