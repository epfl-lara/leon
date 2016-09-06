import leon.lang._
import leon.collection._
import leon._

object ArrayAbs {

  def abs(a: Array[BigInt]): Array[BigInt] = {
    require(a.length > 0)
    val res = Array.fill(a.length)(BigInt(0))
    var i = 0
    (while(i < a.length) {
      val tmp = a(i)
      if(tmp < 0)
        res(i) = -tmp
      else
        res(i) = tmp
      i += 1
    }) invariant(
        i >= 0 &&
        i <= a.length &&
        a.length == res.length &&
        arrayForall(res, 0, i, (x: BigInt) => x >= 0)
      )
    res

  } ensuring(res => arrayForall(res, (x: BigInt) => x >= 0))

  def absBuggy(a: Array[BigInt]): Array[BigInt] = {
    require(a.length > 0 && a.length < 7)
    val res = Array.fill(a.length)(BigInt(0))
    var i = 0
    (while(i < a.length) {
      val tmp = a(i)
      if(tmp < 0)
        res(i) = tmp
      else
        res(i) = tmp
      i += 1
    }) invariant(
        i >= 0 &&
        i <= a.length &&
        a.length == res.length &&
        arrayForall(res, 0, i, (x: BigInt) => x >= 0)
      )
    res

  } ensuring(res => arrayForall(res, (x: BigInt) => x >= 0))

}
