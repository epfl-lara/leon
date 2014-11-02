
object SecondsToTime {

  def toSecs(h: Int, m: Int, s: Int) = h * 3600 + m * 60 + s
  def prop(t: Int, h: Int, m: Int, s: Int) : Boolean = 
    toSecs(h, m, s) == t && 
    m >= 0 && m < 60 && 
    s >= 0 && s < 60 

  def secondsToTime(total : Int) = {
    require(total >= 0)
    rec(total, total, 0, 0)
  } ensuring(_ match { case (h,m,s) => prop(total, h, m, s) })

  def rec(total : Int, r : Int, h : Int, m : Int) : (Int, Int, Int) = {
    require(
      total == toSecs(h, m, r) && 
      m >= 0 && m < 60 && 
      h >= 0 && r >= 0 &&
      (m == 0 || r + m * 60 < 3600)
    )

    if(r >= 3600) {
      rec(total, r - 3600, h + 1, m)
    } else if(r >= 60) {
      rec(total, r - 60, h, m )// FIXME : Should be m + 1
    } else {
      (h, m, r)
    }
  } ensuring { res =>
    val (h,m,s) = res
    prop(total, h, m, s) 
  } 




}
