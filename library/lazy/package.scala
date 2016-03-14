/* Copyright 2009-2013 EPFL, Lausanne */

package leon.lazyeval

import leon.annotation._
import leon.lang._
import scala.language.implicitConversions
import scala.annotation.StaticAnnotation

@library
object $ {
  def apply[T](f: => T) = new $(Unit => f)
  def eager[T](x: => T) = new $(Unit => x)
  /**
   * implicit conversion from eager evaluation to lazy evaluation
   */
  @inline
  implicit def eagerToLazy[T](x: T) = eager(x)

  /**
   * accessing in and out states.
   * Should be used only in ensuring.
   * TODO: enforce this.
   */
  @extern @library
  def inState[T] : Set[$[T]] = sys.error("inState method is not executable!")

  @extern @library
  def outState[T] : Set[$[T]] = sys.error("outState method is not executable")

  /**
   * Helper class for invoking with a given state instead of the implicit state
   */
  @library
  case class WithState[T](v: T) {
    @extern
    def withState[U](u: Set[$[U]]): T = sys.error("withState method is not executable!")

    @extern
    def withState[U, V](u: Set[$[U]], v: Set[$[V]]): T = sys.error("withState method is not executable!")

    @extern
    def withState[U, V, W](u: Set[$[U]], v: Set[$[V]], w: Set[$[W]]): T = sys.error("withState method is not executable!")

    @extern
    def withState[U, V, W, X](u: Set[$[U]], v: Set[$[V]], w: Set[$[W]], x: Set[$[X]]): T = sys.error("withState method is not executable!")
    // extend this to more arguments if needed
  }

  @inline
  implicit def toWithState[T](x: T) = new WithState(x)

  /* @library
  case class Mem[T](v: T) {
    @extern
    def isCached: Boolean = sys.error("not implemented!")
  }
  @inline
  implicit def toMem[T](x: T) = new Mem(x)*/

  /**
   * annotations for monotonicity proofs.
   * Note implemented as of now.
   * Let foo be the method that has the annotation.
   * The given name `methodname` should have the following form:
   *  m(arg1, ..., argn, substate-Set1,..., substate-Setn, superstate-Set1, ..., superstate-Setn)
   */
  @ignore
  class monoproof(methodname: String) extends StaticAnnotation
}

@library
case class $[T](f: Unit => T) {
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
  def isSuspension[T](f: T) : Boolean = sys.error("isSuspensionOf method is not executable")
}

/**
 * The following are set of methods meant for `Memoized` closures
 */
@library
object Mem {
  @inline
  implicit def toMem[T](x: T) = new Mem(x)

  /**
   * accessing in and out states of mems
   * Should be used only in ensuring.
   * TODO: enforce this.
   */
  @extern
  def inState[T] : Set[Mem[T]] = sys.error("inState method is not executable!")

  @extern
  def outState[T] : Set[Mem[T]] = sys.error("outState method is not executable")

  /**
   * Helper class for invoking with a given state instead of the implicit state
   */
  @library
  case class memWithState[T](v: T) {
    @extern
    def withState[U](u: Set[Mem[U]]): T = sys.error("withState method is not executable!")

    @extern
    def withState[U, V](u: Set[Mem[U]], v: Set[Mem[V]]): T = sys.error("withState method is not executable!")

    @extern
    def withState[U, V, W](u: Set[Mem[U]], v: Set[Mem[V]], w: Set[Mem[W]]): T = sys.error("withState method is not executable!")

    @extern
    def withState[U, V, W, X](u: Set[Mem[U]], v: Set[Mem[V]], w: Set[Mem[W]], x: Set[Mem[X]]): T = sys.error("withState method is not executable!")
    // extend this to more arguments if needed
  }

  @inline
  implicit def toWithState[T](x: T) = new memWithState(x)
}

@library
case class Mem[T](v: T) {
  @extern
  def isCached: Boolean = sys.error("not implemented!")
}