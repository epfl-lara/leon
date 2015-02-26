
object SecondsToTime {

  def propSum(t: BigInt, h: BigInt, m: BigInt, s: BigInt) : Boolean = h * 3600 + m * 60 + s == t
  def prop(t: BigInt, h: BigInt, m: BigInt, s: BigInt) : Boolean = propSum(t, h, m, s) && m >= 0 && m < 60 && s >= 0 && s < 60 

  def secondsToTime(total : BigInt) = {
    require(total >= 0)
      rec(total, total, 0, 0)
  } ensuring(_ match { case (h,m,s) => prop(total, h, m, s) }) 

  def secondsToTime2(total : BigInt) = {
    require(total >= 0)
      rec2(total, total, 0, 0)
  } ensuring(_ match { case (h,m,s) => prop(total, h, m, s) }) 

  def rec(total : BigInt, r : BigInt, h : BigInt, m : BigInt) : (BigInt, BigInt, BigInt) = {
    require(propSum(total, h, m, r) && m >= 0 && h >= 0 && r >= 0 && m < 60 && (m == 0 || r + m * 60 < 3600))

    if(r >= 3600) {
      rec(total, r - 3600, h + 1, m)
    } else if(r >= 60) {
      rec(total, r - 60, h, m + 1)
    } else {
      (h, m, r)
    }
  } ensuring(_ match { case(h,m,s) => prop(total, h, m, s) }) 

  def rec2(total : BigInt, r : BigInt, h : BigInt, m : BigInt) : (BigInt, BigInt, BigInt) = {
    require(propSum(total, h, m, r) && m >= 0 && h >= 0 && r >= 0 && m < 60)
    if(r >= 60 && m == 59) {
      rec2(total, r - 60, h + 1, 0)
    } else if(r >= 60) {
      rec2(total, r - 60, h, m + 1)
    } else {
      (h, m, r)
    }
  } ensuring(_ match { case(h,m,s) => prop(total, h, m, s) }) 
}
