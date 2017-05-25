/* Copyright 2009-2013 EPFL, Lausanne */

package leon.mem

import leon.annotation._

@library
@isabelle.typ(name = "Leon_Types.star")
@isabelle.constructor(name = "Leon_Types.star.Star")
case class Star[T](f: T) {
  def * = f
}