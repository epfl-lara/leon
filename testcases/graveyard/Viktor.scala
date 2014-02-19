import leon.lang._

object Viktor {
  def transitive(x: Boolean, y: Boolean, z: Boolean) : Boolean = {
    !(x == y && y == z) || x == z
  } holds

  def doesNotHold1(x: Int, y: Int) : Boolean = {
    x + 2 > y * 2
  } holds
}
