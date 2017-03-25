/* Copyright 2009-2013 EPFL, Lausanne */

package leon.proof.Internal

import leon.annotation._
import leon.lang._
import leon.proof.RelReasoning

import scala.Boolean
import scala.Predef.require

@library
@isabelle.typ(name = "Leon_Types.with_proof")
@isabelle.constructor(name = "Leon_Types.with_proof.With_Proof")
case class WithProof[A, B](x: A, r: (A, B) => Boolean, proof: Boolean, prop: Boolean) {

  /** Close a proof. */
  def |[C](that: WithProof[B, C]): WithProof[B, C] = {
    require(this.prop && this.proof ==> this.r(this.x, that.x))
    WithProof(
      that.x, that.r, that.proof,
      this.prop && this.proof && this.r(this.x, that.x))
  }

  /** Close a proof. */
  def |[C](that: WithRel[B, C]): WithRel[B, C] = {
    require(this.prop && this.proof ==> this.r(this.x, that.x))
    WithRel(
      that.x, that.r,
      this.prop && this.proof && this.r(this.x, that.x))
  }

  /** Close a proof. */
  def |(that: RelReasoning[B]): RelReasoning[B] = {
    require(this.prop && this.proof ==> this.r(this.x, that.x))
    RelReasoning(
      that.x,
      this.prop && this.proof && this.r(this.x, that.x))
  }
}