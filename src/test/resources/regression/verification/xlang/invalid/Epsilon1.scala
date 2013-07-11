/* Copyright 2009-2013 EPFL, Lausanne */

import leon.Utils._

object Epsilon1 {

  def rand2(x: Int): Int = epsilon((y: Int) => true)

  //this should not hold
  def property2(x: Int): Boolean = {
    rand2(x) == rand2(x+1) 
  }.holds

}
