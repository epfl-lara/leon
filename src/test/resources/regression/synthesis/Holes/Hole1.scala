import leon.lang._
import leon.collection._
import leon.lang.synthesis._

object Holes {
  def abs3(a: Int) = {
    if (?(a > 0, a < 0)) {
      a
    } else {
      -a
    }
  } ensuring {
    _ >= 0
  }
}
