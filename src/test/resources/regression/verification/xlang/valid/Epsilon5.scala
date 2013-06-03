/* Copyright 2009-2013 EPFL, Lausanne */

import leon.Utils._

object Epsilon5 {

  def foo(x: Int, y: Int): Int = {
    epsilon((z: Int) => z > x && z < y)
  } ensuring(_ >= x)

}
