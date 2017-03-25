/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import annotation._
import lang._
import scala.language.implicitConversions
import scala.sys

package object lazyeval {

  @library
  def $[T](f: => T) = Lazy(Unit => f)
  //def apply[T](f: => T) = new $(Unit => f)

  // we can duplicate this to handle multiple argument closures
  @library
  def eager[A, R](x: R) = (arg: A) => x

  /**
   * implicit conversion from values to closures.
   * `A` is the argument type, and `R` is the return type
   */
  @library
  @inline
  implicit def eagerToClosure[A, R](x: R) = eager[A, R](x)

  /**
   * For accessing in and out states.
   * Should be used only in ensuring.
   */
  @library
  @extern
  def inState[T]: Set[Lazy[T]] = sys.error("inState method is not executable!")

  @library
  @extern
  def outState[T]: Set[Lazy[T]] = sys.error("outState method is not executable")

  @library
  @inline
  implicit def toWithState[T](x: T) = new WithState(x)


}
