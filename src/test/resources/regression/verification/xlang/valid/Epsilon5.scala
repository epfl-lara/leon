/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._
import leon.lang.xlang._

object Epsilon5 {

  def foo(x: Int, y: Int): Int = {
    epsilon((z: Int) => z > x && z < y)
  } ensuring(_ >= x)

}
