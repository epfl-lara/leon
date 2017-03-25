/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import annotation._
import scala.language.implicitConversions

package object higherorder {

  /**
   * For comparing closures
   */
  @library
  @inline
  implicit def toIs[T](f: T) = Is(f)

  /**
   * For pattern matching on closures
   */
  @library
  @inline
  implicit def toFmatch[T](f: T) = Fmatch(f)

  // Note: this need not be a library function, as it will be inlined anyways
  @inline
  def lift[T](x: T): () => T = {
    () => x
  }
}
