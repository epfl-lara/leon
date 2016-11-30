import leon.lang._

object Overflow13 {

  def foo13(x: Int, y: Int) = {
    require(y != 0)
    x / y
  }

}
