/* Copyright 2009-2013 EPFL, Lausanne */

import leon.Utils._

object Epsilon1 {

  def rand(): Int = epsilon((x: Int) => true)

  //this should hold, that is the expected semantic of our epsilon
  def property1(): Boolean = {
    rand() == rand() 
  }.holds


}
