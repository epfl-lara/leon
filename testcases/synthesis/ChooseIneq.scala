import leon.Utils._

object ChooseIneq {
  def c1(a: Int, b: Int): (Int, Int) = { 
    choose ((x: Int, y: Int) => -3*x + 2*y -b <= a && 2*x - a <= 4*y + b)
  }
}
