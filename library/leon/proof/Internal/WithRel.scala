/* Copyright 2009-2013 EPFL, Lausanne */

package leon.proof.Internal

import leon.annotation._
import leon.lang._
import leon.proof.RelReasoning

import scala.Boolean
import scala.Predef.require

/*** Helper classes for relational reasoning ***/
@library
@isabelle.typ(name = "Leon_Types.with_rel")
@isabelle.constructor(name = "Leon_Types.with_rel.With_Rel")
case class WithRel[A, B](x: A, r: (A, B) => Boolean, prop: Boolean) {

  /** Continue with the next relation. */
  def ^^(y: B): RelReasoning[B] = {
    require(prop ==> r(x, y))
    RelReasoning(y, prop && r(x, y))
  }

  /** Add a proof. */
  def ^^|(proof: Boolean): WithProof[A, B] = {
    require(proof)
    WithProof(x, r, proof, prop)
  }

  /** Short-hand for equational reasoning. */
  def ==|(proof: Boolean): WithProof[A, A] = {
    require(proof)
    WithProof(x, _ == _, proof, prop)
  }

  def qed: Boolean = prop
}