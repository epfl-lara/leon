import leon.lang._

object xplusone {

  def f(n : Int) : Int = {
    if (n > 0) {
      f(n-1) + 1
    } else 1
  } ensuring (rec => rec == n + 1)

  def Sf(n : Int, rec : Int) : Boolean = {
    if (n > 0) {
      val res = epsilon((x:Int) => true)
      Sf(n - 1, res)
      (rec == res + 1)
    } else {
      rec == 1
    }
  } ensuring (_ == (rec == n + 1))

}
