/* Copyright 2009-2013 EPFL, Lausanne */

package leon.proof

import leon.annotation._
import scala.Boolean
import scala.Predef.require

@library
@isabelle.typ(name = "Leon_Types.proof_ops")
@isabelle.constructor(name = "Leon_Types.proof_ops.Proof_Ops")
case class ProofOps(prop: Boolean) {
  def because(proof: Boolean): Boolean = proof && prop
  def neverHolds: Boolean = {
    require(!prop)
    !prop
  }
}