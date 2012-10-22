import leon.Utils._

object ChooseTest {

  def c0(): Int = choose{ (x1: Int) => x1 > 13 }

  def c1(a: Int): Int = choose{ (x1: Int) => x1 > a }
  def c2(a: Int): (Int, Int) = choose{ (x1: Int, x2: Int) => x1 > a && x2 > a }
  def c3(a: Int): (Int, Int, Int) = choose{ (x1: Int, x2: Int, x3: Int) => x1 > a && x2 > a }
  def c4(a: Int): (Int, Int, Int, Int) = choose{ (x1: Int, x2: Int, x3: Int, x4: Int) => x1 > a && x2 > a }
  def c5(a: Int): (Int, Int, Int, Int, Int) = choose{ (x1: Int, x2: Int, x3: Int, x4: Int, x5: Int) => x1 > a && x2 > a }

}
