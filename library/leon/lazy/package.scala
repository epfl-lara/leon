/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import annotation._
import lang._
import scala.language.implicitConversions
import scala.annotation.StaticAnnotation

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

  /**
   * Helper class for invoking with a given state instead of the implicit state
   */
  @library
  @isabelle.typ(name = "Leon_Types.with_state")
  @isabelle.constructor(name = "Leon_Types.with_state.With_State")
  case class WithState[T](v: T) {
    @extern
    def withState[U](u: Set[Lazy[U]]): T = sys.error("withState method is not executable!")

    @extern
    def withState[U, V](u: Set[Lazy[U]], v: Set[Lazy[V]]): T = sys.error("withState method is not executable!")

    @extern
    def withState[U, V, W](u: Set[Lazy[U]], v: Set[Lazy[V]], w: Set[Lazy[W]]): T = sys.error("withState method is not executable!")

    @extern
    def withState[U, V, W, X](u: Set[Lazy[U]], v: Set[Lazy[V]], w: Set[Lazy[W]], x: Set[Lazy[X]]): T = sys.error("withState method is not executable!")
    // extend this to more arguments if needed
  }

  @library
  @inline
  implicit def toWithState[T](x: T) = new WithState(x)

  /**
   * annotations for monotonicity proofs.
   * Note implemented as of now.
   * Let foo be the method that has the annotation.
   * The given name `methodname` should have the following form:
   *  m(arg1, ..., argn, substate-Set1,..., substate-Setn, superstate-Set1, ..., superstate-Setn)
   */
  @ignore
  class monoproof(methodname: String) extends StaticAnnotation

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
    def isSuspension[T](f: T): Boolean = sys.error("isSuspensionOf method is not executable")
  }
}
