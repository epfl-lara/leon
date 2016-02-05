/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers.smtlib

import purescala.Definitions.Program
import purescala.Expressions.Expr

import _root_.smtlib.parser.Commands.{Assert => SMTAssert}
import _root_.smtlib.parser.Terms.{Exists => SMTExists}

class SMTLIBCVC4ProofSolver(context: LeonContext, program: Program) extends SMTLIBCVC4QuantifiedSolver(context, program) {

  override def targetName = "cvc4-proof"

  override def interpreterOps(ctx: LeonContext) = {
    Seq(
      "-q",
      "--print-success",
      "--lang", "smt2.5",
      "--quant-ind",
      "--rewrite-divk",
      "--conjecture-gen",
      "--conjecture-gen-per-round=3",
      "--conjecture-gen-gt-enum=40",
      "--full-saturate-quant"
    ) ++ userDefinedOps(ctx)
  }

  // For this solver, we prefer the variables of assert() commands to be exist. quantified instead of free
  override def assertCnstr(e: Expr) = try {
    emit(SMTAssert(quantifiedTerm(SMTExists, e)(Map())))
  } catch {
    case _ : SMTLIBUnsupportedError =>
      addError()
  }

  // This solver does not support model extraction
  override def getModel: solvers.Model = {
    // We don't send the error through reporter because it may be caught by PortfolioSolver
    throw LeonFatalError(Some(s"Solver $name does not support model extraction."))
  }

  protected val allowQuantifiedAssertions: Boolean = true
}
