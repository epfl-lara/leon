/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package smtlib

import purescala.Definitions.Program

class SMTLIBCVC4CounterExampleSolver(context: SolverContext, program: Program) extends SMTLIBCVC4QuantifiedSolver(context, program) {

  override def targetName = "cvc4-cex"

  override def interpreterOps(ctx: LeonContext) = {
    Seq(
      "-q",
      "--rewrite-divk",
      "--produce-models",
      "--print-success",
      "--lang", "smt2.5",
      "--fmf-fun"
    ) ++ userDefinedOps(ctx)
  }

  protected val allowQuantifiedAssertions: Boolean = false
}
