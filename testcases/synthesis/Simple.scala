import leon.lang._
import leon.lang.synthesis._

object SimpleSynthesis {

  def c1(x: Int): Int = choose { (y: Int) => y > x }

}
