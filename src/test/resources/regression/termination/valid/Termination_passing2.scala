import leon.Utils._

object Termination {
  def f1(x: Int, b: Boolean) : Int = {
    if (b) f2(x)
    else f3(x)
  }

  def f2(x: Int) : Int = {
    if (x < 0) 0
    else f1(x - 1, true)
  }

  def f3(x: Int) : Int = {
    if (x > 0) 0
    else f1(x + 1, false)
  }
}

// vim: set ts=4 sw=4 et:
