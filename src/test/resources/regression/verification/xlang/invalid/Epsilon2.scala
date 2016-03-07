/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.lang.xlang._

object Epsilon2 {

  def rand3(x: Int): Int = epsilon((y: Int) => x == x)

  //this should not hold
  def property3(x: Int): Boolean = {
    rand3(x) == rand3(x+1)
  }.holds
}
