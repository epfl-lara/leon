/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.lang.xlang._

object Epsilon7 {

  def rand(): Int = epsilon((x: Int) => true)

  //this used to be VALID until the introduction
  //of a global state that can tracks epsilon calls
  //and ensure each epsilon is invoked with a different
  //seed value
  def wrongProperty1(): Boolean = {
    rand() == rand() 
  }.holds


}
