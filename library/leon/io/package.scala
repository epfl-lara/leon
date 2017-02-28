/* Copyright 2009-2016 EPFL, Lausanne */

package leon

package object io {

  import leon.annotation._

  @library
  @cCode.typedef(alias = "void*")
  case class State(var seed: BigInt)

  @library
  @cCode.function(code = "static void* __FUNCTION__(void) { return NULL; }")
  def newState: State = State(0)

}

