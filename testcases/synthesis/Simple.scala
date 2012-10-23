import leon.Utils._

object SimpleSynthesis {

  def c1(x: Int): Int = choose { (y: Int) => y > x }

}
