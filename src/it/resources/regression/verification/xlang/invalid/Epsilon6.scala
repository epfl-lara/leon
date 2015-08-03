/* Copyright 2009-2015 EPFL, Lausanne */

import leon.lang._
import leon.lang.xlang._

object Epsilon6 {

  def greaterWrong(x: Int): Int = {
    epsilon((y: Int) => y >= x)
  } ensuring(_ > x)

}
