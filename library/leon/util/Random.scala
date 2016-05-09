/* Copyright 2009-2016 EPFL, Lausanne */

package leon.util

import leon.annotation._
import leon.lang.xlang._

object Random {

  @library
  @isabelle.noBody()
  def nextBoolean(): Boolean = epsilon((x: Boolean) => true)

  @library
  @isabelle.noBody()
  def nextInt(): Int = epsilon((x: Int) => true)

  @library
  @isabelle.noBody()
  def nextInt(max: Int): Int = {
    require(max > 0)
    epsilon((x: Int) => x >= 0 && x < max)
  } ensuring(res => res >= 0 && res < max)

  @library
  @isabelle.noBody()
  def nextBigInt(): BigInt = epsilon((x: BigInt) => true)

  @library
  @isabelle.noBody()
  def nextBigInt(max: BigInt): BigInt = {
    require(max > 0)
    epsilon((x: BigInt) => x >= 0 && x < max)
  } ensuring(res => res >= 0 && res < max)

}
