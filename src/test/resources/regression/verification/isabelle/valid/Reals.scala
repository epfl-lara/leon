import leon._
import leon.lang._
import leon.annotation._

object Reals {

  def comm(x: Real, y: Real) =
    (x + y == y + x).holds

  def assoc(x: Real, y: Real, z: Real) =
    ((x * y) * z == x * (y * z)).holds

}
