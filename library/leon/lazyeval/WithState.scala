/* Copyright 2009-2013 EPFL, Lausanne */

package leon.lazyeval

import leon.annotation._
import leon.lang._
import scala.sys

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
