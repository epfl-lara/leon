/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers.smtlib

import leon.purescala.Common.Identifier
import leon.purescala.Definitions.Program
import leon.purescala.Expressions.Expr
import smtlib.parser.Commands.{Assert => SMTAssert}
import smtlib.parser.Terms.Exists

class SMTLIBCVC4ProofSolver(context: LeonContext, program: Program) extends SMTLIBCVC4QuantifiedSolver(context, program) {

  override def targetName = "cvc4-proof"

  override def interpreterOps(ctx: LeonContext) = {
    Seq(
      "-q",
      "--print-success",
      "--lang", "smt",
      "--quant-ind",
      "--rewrite-divk",
      "--conjecture-gen",
      "--conjecture-gen-per-round=3",
      "--conjecture-gen-gt-enum=40",
      "--full-saturate-quant"
    ) ++ userDefinedOps(ctx)
  }

  // For this solver, we prefer the variables of assert() commands to be exist. quantified instead of free
  override def assertCnstr(expr: Expr) =
    try {
      sendCommand(SMTAssert(quantifiedTerm(Exists, expr)))
    } catch {
      case _ : IllegalArgumentException =>
        addError()
    }

  // This solver does not support model extraction
  override def getModel: Map[Identifier, Expr] = {
    reporter.warning(s"Solver $name does not support model extraction.")
    Map()
  }

  // FIXME: mk: This is kind of hiding the problem under the carpet.
  // We could just return an empty counterexample, but this breaks PortfolioSolver
  override def check: Option[Boolean] = {
    super.check match {
      case Some(true) =>
        reporter.warning(s"Solver $name found a counterexample, but masking it as unknown because counterexamples are not supported.")
        None
      case other => other
    }
  }
}
