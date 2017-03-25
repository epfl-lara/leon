/* Copyright 2009-2016 EPFL, Lausanne */

package leon

import leon.annotation._
import scala.language.implicitConversions
import scala.Boolean
import scala.Predef.require

package object proof {

  @library
  implicit def boolean2ProofOps(prop: Boolean): ProofOps = ProofOps(prop)

  @library
  def trivial: Boolean = true

  @library
  def by(proof: Boolean)(prop: Boolean): Boolean =
    proof && prop

  @library
  def check(prop: Boolean): Boolean = {
    require(prop)
    prop
  }

  @library
  implicit def any2RelReasoning[A](x: A): RelReasoning[A] =
    RelReasoning(x, true)

}

