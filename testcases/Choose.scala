import leon.Utils._

object ChooseTest {

  def c1(x: Int): Int = choose{ (a1: Int) => a1 > x }
  def c2(x: Int): (Int, Int) = choose{ (a1: Int, a2: Int) => a1 > x && a2 > x }
  def c3(x: Int): (Int, Int, Int) = choose{ (a1: Int, a2: Int, a3: Int) => a1 > x && a2 > x }
  def c4(x: Int): (Int, Int, Int, Int) = choose{ (a1: Int, a2: Int, a3: Int, a4: Int) => a1 > x && a2 > x }
  def c5(x: Int): (Int, Int, Int, Int, Int) = choose{ (a1: Int, a2: Int, a3: Int, a4: Int, a5: Int) => a1 > x && a2 > x }

}
