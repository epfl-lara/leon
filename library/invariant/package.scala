/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import leon.annotation._
import leon.lang._
import scala.language.implicitConversions

package object invariant {
  @library
  def tmpl(templateFunc: BigInt => Boolean): Boolean = true
  @library
  def tmpl(templateFunc: (BigInt, BigInt) => Boolean): Boolean = true
  @library
  def tmpl(templateFunc: (BigInt, BigInt, BigInt) => Boolean): Boolean = true
  @library
  def tmpl(templateFunc: (BigInt, BigInt, BigInt, BigInt) => Boolean): Boolean = true
  @library
  def tmpl(templateFunc: (BigInt, BigInt, BigInt, BigInt, BigInt) => Boolean): Boolean = true

  @library
  def ? : BigInt = 0

  @library
  def ?(id: BigInt) = id
}
