/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package smtlib

import OptionParsers._

import solvers.theories._
import purescala.Definitions.Program

class SMTLIBCVC4Solver(context: SolverContext, program: Program)
  extends SMTLIBSolver(context, program, new BagEncoder(context.context, program))
     with SMTLIBCVC4Target
     with cvc4.CVC4Solver {

  def targetName = "cvc4"

  def userDefinedOps(ctx: LeonContext) = {
    ctx.findOptionOrDefault(SMTLIBCVC4Component.optCVC4Options)
  }

  def interpreterOps(ctx: LeonContext) = {
    Seq(
      "-q",
      "--produce-models",
      "--incremental",
//      "--no-incremental",
//      "--tear-down-incremental",
//      "--dt-rewrite-error-sel", // Removing since it causes CVC4 to segfault on some inputs
      "--rewrite-divk",
      "--print-success",
      "--lang", "smt2.5"
    ) ++ userDefinedOps(ctx).toSeq
  }
}

object SMTLIBCVC4Component extends LeonComponent {
  val name = "CVC4 solver"

  val description = "Solver invoked with --solvers=smt-cvc4"

  val optCVC4Options = new LeonOptionDef[Set[String]] {
    val name = "solver:cvc4"
    val description = "Pass extra arguments to CVC4"
    val default = Set[String]()
    val parser = setParser(stringParser)
    val usageRhs = "<cvc4-opt>"
  }

  override val definedOptions : Set[LeonOptionDef[Any]] = Set(optCVC4Options)
}
