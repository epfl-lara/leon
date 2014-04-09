/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._
import leon.lang.xlang._

object Epsilon3 {

  def posWrong(): Int = {
    epsilon((y: Int) => y >= 0)
  } ensuring(_ > 0)

}
