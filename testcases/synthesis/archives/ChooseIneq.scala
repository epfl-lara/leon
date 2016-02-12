import leon.lang._
import leon.lang.synthesis._

object ChooseIneq {
  def c1(a: Int, b: Int): (Int, Int) = { 
    choose ((x: Int, y: Int) => -3*x + 2*y -b <= a && 2*x - a <= 4*y + b)
  }

  def c2(a : Int) : (Int, Int) = choose {
    (x : Int, y : Int) => 5*x + 7*y == a && 0 <= x && x <= y
  }
}
