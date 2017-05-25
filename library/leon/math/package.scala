/* Copyright 2009-2016 EPFL, Lausanne */

package leon
import leon.annotation._
import scala.{BigInt,Int}

package object math {

  @library
  def min(i1: Int, i2: Int) = if (i1 <= i2) i1 else i2

  @library
  def max(i1: Int, i2: Int) = if (i1 >= i2) i1 else i2

  @library
  def min(i1: BigInt, i2: BigInt) = if (i1 <= i2) i1 else i2

  @library
  def max(i1: BigInt, i2: BigInt) = if (i1 >= i2) i1 else i2

  @library
  def abs(n: BigInt) = if(n < 0) -n else n
}
