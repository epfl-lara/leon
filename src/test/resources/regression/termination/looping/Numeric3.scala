import leon.Utils._

object Numeric3 {
  def looping(x: Int) : Int = if (x > 0) looping(x - 1) else looping(5)
}


// vim: set ts=4 sw=4 et:
