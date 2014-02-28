import leon.lang._

object Test {
  def test(x: Int, y: Int) = choose((z: Int) => z >= x && z >= y && (z == x || z == y))
}
