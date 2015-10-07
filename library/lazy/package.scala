/* Copyright 2009-2013 EPFL, Lausanne */

package leon.lazyeval

import leon.annotation._
import leon.lang._
import scala.language.implicitConversions

@library
object $ {
  def apply[T](f: => T) = new $(Unit => f)
}

@library
case class $[T](f: Unit => T) { // leon does not support call by name as of now
  lazy val value = f(())
  def *  = f(())
  def isEvaluated = true // for now this is a dummy function, but it will be made sound when leon supports mutable fields.
}
