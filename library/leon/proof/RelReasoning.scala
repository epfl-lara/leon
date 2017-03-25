/* Copyright 2009-2013 EPFL, Lausanne */

package leon.proof

import leon.annotation._
import scala.Boolean
import scala.Predef.require

/**
  * Relational reasoning.
  *
  *         {
  *           ((y :: ys) :+ x).last   ^^ _ == _ ^^| trivial         |
  *           (y :: (ys :+ x)).last   ==| trivial         |
  *           (ys :+ x).last          ==| snocLast(ys, x) |
  *           x
  *         }.qed
  */
@library
@isabelle.typ(name = "Leon_Types.rel_reasoning")
@isabelle.constructor(name = "Leon_Types.rel_reasoning.Rel_Reasoning")
case class RelReasoning[A](x: A, prop: Boolean) {

  def ^^[B](r: (A, B) => Boolean): Internal.WithRel[A, B] = Internal.WithRel(x, r, prop)

  /** Short-hand for equational reasoning. */
  def ==|(proof: Boolean): Internal.WithProof[A, A] = {
    require(proof)
    Internal.WithProof(x, _ == _, proof, prop)
  }

  def qed: Boolean = prop
}