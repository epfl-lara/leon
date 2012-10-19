import leon.Utils._

object Abs {

  def abs(x: Int): Int = choose{ x: Int => x > 0 }

}
