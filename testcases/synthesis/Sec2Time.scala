import leon.lang._
import leon.lang.synthesis._

object Sec2Time {

  def s2t(total: Int) : (Int, Int, Int) = 
    choose((h: Int, m: Int, s: Int) => 
      3600*h + 60*m + s == total && 
      h >= 0 && m >= 0 && m < 60 && s >= 0 && s < 60
    )

}
