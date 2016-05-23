/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.lang.xlang._

object Epsilon8 {

  def wrongProp: Boolean = {
    epsilon((y: Int) => true) == epsilon((y: Int) => true)
  } holds

}
