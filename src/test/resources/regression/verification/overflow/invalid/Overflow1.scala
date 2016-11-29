import leon.lang._

object Overflow1 {

  def foo(x: Int): Int = {
    x + 1
  }

  def foo2(x: Int): Int = {
    x + (-1)
  }

  def foo3(x: Int): Int = {
    x - 1
  }

  def foo4(x: Int): Int = {
    x - (-1)
  }

  def foo5(x: Int, y: Int): Int = {
    x + y
  }

  def foo6(x: Int, y: Int): Int = {
    x - y
  }

  def foo7(x: Int): Int = {
    x*2
  }

  def foo8(x: Int): Int = {
    x*3
  }

  def foo9(x: Int): Int = {
    x*4
  }

  def foo10(x: Int, y: Int): Int = {
    x*y
  }

  def foo11(): Int = {
    val x = 500000
    val y = 500000
    x*y
  }

  def foo12(x: Int): Int = {
    -x
  }

  def foo13(x: Int, y: Int) = {
    require(y != 0)
    x / y
  }

}
