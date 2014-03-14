/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._

object Numeric {
  // division by 0 loops
  def looping(x: Int, y: Int): Int = {
    if (x < y) 0
    else 1 + looping(x - y, y)
  }
}

// vim: set ts=4 sw=4 et:
