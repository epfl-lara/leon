import leon.lang._

object StrictArithmetic1 {

  def foo(x: Int, y: Int) = {
    x << y
  }

  def foo2(x: Int, y: Int) = {
    x >> y
  }

  def foo3(x: Int, y: Int) = {
    x >>> y
  }

}

