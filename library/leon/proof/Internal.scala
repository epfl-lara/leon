/* Copyright 2009-2016 EPFL, Lausanne */
package leon.proof

import leon.lang._
import leon.annotation._

/** Internal helper classes and methods for the 'proof' package. */
object Internal {

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

  @library
  @isabelle.typ(name = "Leon_Types.with_proof")
  @isabelle.constructor(name = "Leon_Types.with_proof.With_Proof")
  case class WithProof[A, B](
    x: A, r: (A, B) => Boolean, proof: Boolean, prop: Boolean) {

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
}
