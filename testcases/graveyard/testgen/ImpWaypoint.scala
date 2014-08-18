
import leon.lang._
import leon.annotation._

object Imp {

  @main
  def foo(i: Int): Int = {
    var a = 0
    a = a + 3
    if(i < a)
      waypoint(1, a = a + 1)
    else
      a = a - 1
    a
  } ensuring(_  >= 0)

}

// vim: set ts=4 sw=4 et:
