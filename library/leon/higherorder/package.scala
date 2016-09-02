/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import annotation._
import lang._
import scala.language.implicitConversions
import scala.annotation.StaticAnnotation

package object higherorder {

  /**
   * For comparing closures
   */
  @library
  @inline
  implicit def toIs[T](f: T) = Is(f)

  @library
  case class Is[T](f: T) {
    @extern
    @library
    def is[U](f: U): Boolean = sys.error("Can't execute the construct")
  }

  /**
   * For pattern matching on closures
   */
  @library
  @inline
  implicit def toFmatch[T](f: T) = Fmatch(f)

  @library
  case class Fmatch[T](f: T) {
    @extern
    @library
    def fmatch[A, R](pf: A  =>  R): R = sys.error("Can't execute the construct")
    @extern
    @library
    def fmatch[A, B, R](pf: (A, B)  =>  R): R = sys.error("Can't execute the construct")
    @extern
    @library
    def fmatch[A, B, C, R](pf: (A, B, C)  =>  R): R = sys.error("Can't execute the construct")
    @extern
    @library
    def fmatch[A, B, C, D, R](pf: (A, B, C, D)  =>  R): R = sys.error("Can't execute the construct")
  }

  // Note: this need not be a library function, as it will be inlined anyways
  @inline
  def lift[T](x: T): () => T = {
    () => x
  }
}
