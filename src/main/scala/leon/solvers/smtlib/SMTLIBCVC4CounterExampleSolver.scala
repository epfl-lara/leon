/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers.smtlib

import purescala.Definitions.Program

class SMTLIBCVC4CounterExampleSolver(context: LeonContext, program: Program) extends SMTLIBCVC4QuantifiedSolver(context, program) {

  override val targetName = "cvc4-cex"

  override def interpreterOps(ctx: LeonContext) = {
    Seq(
      "-q",
      "--produce-models",
      "--print-success",
      "--lang", "smt",
      "--fmf-fun"
    ) ++ userDefinedOps(ctx)
  }

}
