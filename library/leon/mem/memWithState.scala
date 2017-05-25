/* Copyright 2009-2013 EPFL, Lausanne */

package leon.mem

import leon.annotation._
import leon.lang._
import scala.sys

/**
  * Helper class for invoking with a given state instead of the implicit state
  */
@library
@isabelle.typ(name = "Leon_Types.mem_with_state")
@isabelle.constructor(name = "Leon_Types.mem_with_state.Mem_With_State")
case class memWithState[T](v: T) {
  @extern
  def in[U](u: Set[Fun[U]]): T = sys.error("in method is not executable!")
}