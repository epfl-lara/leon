import leon.Utils._

object Epsilon5 {

  def foo(x: Int, y: Int): Int = {
    epsilon((z: Int) => z > x && z < y)
  } ensuring(_ >= x)

  def fooWrong(x: Int, y: Int): Int = {
    epsilon((z: Int) => z >= x && z <= y)
  } ensuring(_ > x)

}

// vim: set ts=4 sw=4 et:
