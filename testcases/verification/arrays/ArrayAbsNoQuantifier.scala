import leon.lang._

object AbsFun {


  def abs(tab: Array[BigInt]): Array[BigInt] = {
    require(tab.length >= 0)
    val t = while0(Array.fill(tab.length)(0), 0, tab)
    t._1
  } ensuring(res => isPositive(res, res.length))


  def while0(t: Array[BigInt], k: Int, tab: Array[BigInt]): (Array[BigInt], Int) = {
    require(tab.length >= 0 && 
            t.length == tab.length && 
            k >= 0 &&
            k <= tab.length && 
            isPositive(t, k))
    
    if(k < tab.length) {
      val nt = t.updated(k, if(tab(k) < 0) -tab(k) else tab(k))
      while0(nt, k+1, tab)
    } else {
      (t, k)
    }
  } ensuring(res => 
      res._2 >= tab.length &&
      res._1.length == tab.length &&
      res._2 >= 0 &&
      res._2 <= tab.length &&
      isPositive(res._1, res._2))

  def property(t: Array[BigInt], k: Int): Boolean = {
    require(isPositive(t, k) && t.length >= 0 && k >= 0 && t.length < 6)
    if(k < t.length) {
      val nt = t.updated(k, if(t(k) < 0) -t(k) else t(k))
      isPositive(nt, k+1)
    } else true
  } holds


  def isPositive(a : Array[BigInt], size : Int) : Boolean = {
    require(a.length >= 0 && size <= a.length)
    rec(0, a, size)
  }
  def rec(i: Int, a: Array[BigInt], size: Int) : Boolean = {
    require(a.length >= 0 && size <= a.length && i >= 0)

    if(i >= size) true
    else {
      if (a(i) < 0)
        false
      else
        rec(i + 1, a, size)
    }
  }

  def testArrayPos: Boolean = {
    val a = Array[BigInt](1,2,3,4,5)
    isPositive(a, 5)
  } holds
  def testArrayNotPos: Boolean = {
    val a = Array[BigInt](1,2,-3,4,5)
    !isPositive(a, 5)
  } holds

}
