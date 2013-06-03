/* Copyright 2009-2013 EPFL, Lausanne */

import leon.Utils._

object Epsilon3 {

  def pos(): Int = {
    epsilon((y: Int) => y > 0)
  } ensuring(_ >= 0)

}
