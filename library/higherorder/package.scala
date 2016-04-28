/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import annotation._
import lang._
import scala.language.implicitConversions
import scala.annotation.StaticAnnotation

package object higherorder {

  @library
  @extern
  def exists[A](p: A => Boolean): Boolean = sys.error("Can't execute quantified proposition")
  @library
  @extern
  def exists[A,B](p: (A,B) => Boolean): Boolean = sys.error("Can't execute quantified proposition")
  @library
  @extern
  def exists[A,B,C](p: (A,B,C) => Boolean): Boolean = sys.error("Can't execute quantified proposition")
  @library
  @extern
  def exists[A,B,C,D](p: (A,B,C,D) => Boolean): Boolean = sys.error("Can't execute quantified proposition")
  @library
  @extern
  def exists[A,B,C,D,E](p: (A,B,C,D,E) => Boolean): Boolean = sys.error("Can't execute quantified proposition")

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
    def fmatch[V](pf: Any =>  V) = sys.error("Can't execute the construct")
  }
}