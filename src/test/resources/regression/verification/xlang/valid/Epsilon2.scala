/* Copyright 2009-2014 EPFL, Lausanne */

import leon.lang._
import leon.lang.xlang._

object Epsilon1 {

  def rand(): Int = epsilon((x: Int) => true)

  //this should hold, that is the expected semantic of our epsilon
  def property1(): Boolean = {
    rand() == rand() 
  }.holds


}
