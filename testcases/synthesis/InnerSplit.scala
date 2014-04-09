import leon.lang._
import leon.lang.synthesis._

object Test {
  def test(x: Int, y: Int) = choose((z: Int) => z >= x && z >= y && (z == x || z == y))
}
