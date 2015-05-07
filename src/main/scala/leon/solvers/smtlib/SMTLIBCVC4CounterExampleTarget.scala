/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers.smtlib

import purescala.Common.FreshIdentifier
import purescala.Expressions.{FunctionInvocation, BooleanLiteral, Expr, Implies}
import purescala.Definitions.TypedFunDef
import purescala.Constructors.application
import purescala.DefOps.typedTransitiveCallees
import leon.purescala.ExprOps.matchToIfThenElse
import smtlib.parser.Commands._
import smtlib.parser.Terms._

trait SMTLIBCVC4CounterExampleTarget extends SMTLIBCVC4QuantifiedTarget {
  this: SMTLIBSolver =>

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
