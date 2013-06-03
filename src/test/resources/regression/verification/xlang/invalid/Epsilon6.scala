/* Copyright 2009-2013 EPFL, Lausanne */

import leon.Utils._

object Epsilon6 {

  def greaterWrong(x: Int): Int = {
    epsilon((y: Int) => y >= x)
  } ensuring(_ > x)

}
