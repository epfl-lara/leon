import leon.lang._
import leon.lang.synthesis._

object ChooseArith {
  def c1(a : Int) : (Int, Int) = 
    choose((x:Int,y:Int) => 2*x + 4*a == -y)
}
