import leon.lang._

object Overflow1 {

  def foo(x: Int): Int = {
    require(x < 100)
    x + 1
  }

  def foo2(x: Int): Int = {
    require(x > -100)
    x + (-1)
  }

  def foo3(x: Int): Int = {
    require(x > -100)
    x - 1
  }

  def foo4(x: Int): Int = {
    require(x < 100)
    x - (-1)
  }

  def foo5(x: Int, y: Int): Int = {
    require(x < 0 && y > 0)
    x + y
  }

  def foo6(x: Int, y: Int): Int = {
    require(x > 0 && y > 0)
    x - y
  }

  def foo7(x: Int): Int = {
    require(x > -100 && x < 100)
    x*2
  }

  def foo8(x: Int): Int = {
    require(x > -100 && x < 100)
    x*3
  }

  def foo10(x: Int, y: Int): Int = {
    require(x >= -10 && x <= 10 && y >= -10 && y <= 10)
    x*y
  }

  //def foo11(): Int = {
  //  val x = 500000
  //  val y = 500000
  //  x*y
  //}

  def foo12(x: Int): Int = {
    require(x != -2147483648) // -2^31
    -x
  }

  def foo13(x: Int, y: Int) = {
    require(y != 0 && (x != -2147483648 || y != -1))
    x / y
  }

}
