/* Copyright 2009-2013 EPFL, Lausanne */

package leon.mem

import leon.annotation._

/**
  * A class representing named function calls. These are entities that are memoized.
  * This should be applied only over a function invocation or lambda application.
  */
@library
@isabelle.typ(name = "Leon_Types.fun")
@isabelle.constructor(name = "Leon_Types.fun.Fun")
case class Fun[T](v: T)
