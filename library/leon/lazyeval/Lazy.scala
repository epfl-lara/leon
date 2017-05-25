/* Copyright 2009-2013 EPFL, Lausanne */

package leon.lazyeval

import leon.annotation._
import scala.{sys,Boolean,Unit}

@library
@isabelle.typ(name = "Leon_Types.lazy")
@isabelle.constructor(name = "Leon_Types.lazy.Lazy")
case class Lazy[T](f: Unit => T) {
  @extern
  lazy val value = {
    val x = f(())
    eval = true
    x
  }
  def * = f(())

  @ignore
  var eval = false // is this thread safe ?

  @extern
  def isEvaluated = eval

  @extern
  def isSuspension[F](f: F): Boolean = sys.error("isSuspensionOf method is not executable")
}