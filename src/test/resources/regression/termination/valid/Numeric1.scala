import leon.lang._

object Numeric {

  def f1(x: Int): Int = f2(x - 2)

  def f2(x: Int): Int = if (x < 0) 0 else f1(x + 1)
}


// vim: set ts=4 sw=4 et:
