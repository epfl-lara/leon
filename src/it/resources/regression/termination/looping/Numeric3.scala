/* Copyright 2009-2015 EPFL, Lausanne */

import leon.lang._

object Numeric3 {
  def looping(x: Int) : Int = if (x > 0) looping(x - 1) else looping(5)
}


// vim: set ts=4 sw=4 et:
