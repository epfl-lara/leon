/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import leon.annotation._
import leon.lang._
import scala.language.implicitConversions

package object instrumentation {
  @library
  def time: BigInt = 0

  @library
  def stack: BigInt = 0

  @library
  def rec: BigInt = 0

  @library
  def depth: BigInt = 0

  @library
  def tpr: BigInt = 0
}
