/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._

object Numeric3 {
  def unknown(x: Int) : Int = if (x > 0) unknown(x - 1) else unknown(5)
}


// vim: set ts=4 sw=4 et:
