/* Copyright 2009-2013 EPFL, Lausanne */

package leon.higherorder

import leon.annotation._
import scala.{sys,Boolean}

@library
case class Is[T](f: T) {
  @extern
  @library
  def is[U](f: U): Boolean = sys.error("Can't execute the construct")
}
