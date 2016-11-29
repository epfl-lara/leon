import leon.lang._

object StrictArithmetic1 {

  def foo(x: Int, y: Int) = {
    require(0 <= y && y <= 31)
    x << y
  }

  def foo2(x: Int, y: Int) = {
    require(0 <= y && y <= 31)
    x >> y
  }

  def foo3(x: Int, y: Int) = {
    require(0 <= y && y <= 31)
    x >>> y
  }

  def foo4(x: Int, y: Int) = {
    require(y != 0 && (x != -2147483648 || y != -1))
    x % y
  }

}

