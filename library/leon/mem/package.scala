/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import annotation._
import lang._
import scala.language.implicitConversions
import scala.annotation.StaticAnnotation

package object mem {

  @library
  @inline
  implicit def toMem[T](x: T) = new Mem(x)

  /**
   * accessing in and out states of mems
   * Should be used only in ensuring.
   */
  @library
  @extern
  def inState[T]: Set[Mem[T]] = sys.error("inState method is not executable!")

  @library
  @extern
  def outState[T]: Set[Mem[T]] = sys.error("outState method is not executable")

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

  @library
  @inline
  implicit def toWithState[T](x: T) = new memWithState(x)

  @library
  case class Mem[T](v: T) {
    @extern
    def isCached: Boolean = sys.error("not implemented!")
  }
}