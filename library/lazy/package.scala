/* Copyright 2009-2013 EPFL, Lausanne */

package leon.lazyeval

import leon.annotation._
import leon.lang._
import scala.language.implicitConversions

@library
object $ {
  def apply[T](f: => T) = new $(Unit => f)
  def eager[T](x: => T) = new $(Unit => x)
  /**
   * implicit conversion from eager evaluation to lazy evaluation
   */
  @inline //inlining call-by-name here
  implicit def eagerToLazy[T](x: T) = eager(x)
}

@library
case class $[T](f: Unit => T) { // leon does not support call by name as of now
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
}
