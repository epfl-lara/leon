
object SecondsToTime {

  def toSecs(h: Int, m: Int, s: Int) = h * 3600 + m * 60 + s
  def prop(t: Int, h: Int, m: Int, s: Int) : Boolean = 
    toSecs(h, m, s) == t && 
    m >= 0 && m < 60 && 
    s >= 0 && s < 60 

  def secondsToTime(total : Int) = {
    require(total >= 0)
    val h = total / 3600
    val rest = total % 3600
    val m = rest / 60
    val s = rest % 60
    (h,m,s)
  } ensuring { _ match { case (h,m,s) =>
    prop(total, h, m, s)
  }}


}
