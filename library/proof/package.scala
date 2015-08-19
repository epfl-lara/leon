/* Copyright 2009-2014 EPFL, Lausanne */
package leon

import leon.annotation._
import leon.lang._
import scala.language.implicitConversions

import leon.proof.Internal._

package object proof {

  case class ProofOps(prop: Boolean) {
    def because(proof: Boolean): Boolean = proof && prop
    def neverHolds: Boolean = {
      require(!prop)
      !prop
    }
  }

  implicit def boolean2ProofOps(prop: Boolean): ProofOps = ProofOps(prop)

  def trivial: Boolean = true

  def by(proof: Boolean)(prop: Boolean): Boolean =
    proof && prop

  def check(prop: Boolean): Boolean = {
    require(prop)
    prop
  }

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
  case class RelReasoning[A](x: A, prop: Boolean) {

    def ^^[B](r: (A, B) => Boolean): WithRel[A, B] = WithRel(x, r, prop)

    /** Short-hand for equational reasoning. */
    def ==|(proof: Boolean): WithProof[A, A] = {
      require(proof)
      WithProof(x, _ == _, proof, prop)
    }

    def qed: Boolean = prop
  }

  implicit def any2RelReasoning[A](x: A): RelReasoning[A] =
    RelReasoning(x, true)

}

