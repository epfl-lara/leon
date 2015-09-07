/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers.smtlib

import OptionParsers._

import purescala.Definitions.Program

class SMTLIBCVC4Solver(context: LeonContext, program: Program) extends SMTLIBSolver(context, program) with SMTLIBCVC4Target {

  def targetName = "cvc4"

  def userDefinedOps(ctx: LeonContext) = {
    ctx.findOptionOrDefault(SMTLIBCVC4Component.optCVC4Options)
  }

  def interpreterOps(ctx: LeonContext) = {
    Seq(
      "-q",
      "--produce-models",
      "--no-incremental",
      "--tear-down-incremental",
      "--rewrite-divk",
      "--print-success",
      "--lang", "smt"
    ) ++ userDefinedOps(ctx).toSeq
  }
}

object SMTLIBCVC4Component extends LeonComponent {
  val name = "cvc4 solver"

  val description = "Solver invoked when --solvers=smt-cvc4"

  val optCVC4Options = new LeonOptionDef[Set[String]] {
    val name = "solver:cvc4"
    val description = "Pass extra arguments to CVC4"
    val default = Set[String]()
    val parser = setParser(stringParser)
    val usageRhs = "<cvc4-opt>"
  }

  override val definedOptions : Set[LeonOptionDef[Any]] = Set(optCVC4Options)
}
