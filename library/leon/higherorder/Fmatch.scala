/* Copyright 2009-2013 EPFL, Lausanne */

package leon.higherorder

import leon.annotation._
import scala.sys

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
