/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers.smtlib

import leon.purescala.Definitions.Program

class SMTLIBCVC4ProofTarget(context: LeonContext, program: Program) extends SMTLIBCVC4QuantifiedTarget(context, program) {

  override val targetName = "cvc4-proof"

  override def interpreterOps(ctx: LeonContext) = {
    Seq(
      "-q",
      "--print-success",
      "--lang", "smt",
      "--quant-ind",
      "--conjecture-gen",
      "--conjecture-gen-per-round=3",
      "--conjecture-gen-gt-enum=40",
      "--full-saturate-quant"
    ) ++ userDefinedOps(ctx)
  }

}
