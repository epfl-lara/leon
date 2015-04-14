/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers

import purescala.Definitions._
import scala.reflect.runtime.universe._

abstract class SolverFactory[+S <: Solver : TypeTag] {
  def getNewSolver(): S

  val name = typeOf[S].toString.split("\\.").last.replaceAll("Solver", "")+"*"
}

object SolverFactory {
  def apply[S <: Solver : TypeTag](builder: () => S): SolverFactory[S] = {
    new SolverFactory[S] {
      def getNewSolver() = builder()
    }
  }

  val definedSolvers = Set("fairz3", "unrollz3", "enum", "smt", "smt-z3", "smt-z3-quantified", "smt-cvc4", "smt-2.5-cvc4")

  def getFromSettings[S](ctx: LeonContext, program: Program): SolverFactory[TimeoutSolver] = {
    import combinators._
    import z3._
    import smtlib._

    def getSolver(name: String): SolverFactory[TimeoutSolver] = name match {
      case "fairz3" =>
        SolverFactory(() => new FairZ3Solver(ctx, program) with TimeoutSolver)

      case "unrollz3" =>
        SolverFactory(() => new UnrollingSolver(ctx, program, new UninterpretedZ3Solver(ctx, program)) with TimeoutSolver)

      case "enum"   =>
        SolverFactory(() => new EnumerationSolver(ctx, program) with TimeoutSolver)

      case "smt" | "smt-z3" =>
        SolverFactory(() => new UnrollingSolver(ctx, program, new SMTLIBSolver(ctx, program) with SMTLIBZ3Target) with TimeoutSolver)

      case "smt-z3-quantified" =>
        SolverFactory(() => new SMTLIBSolver(ctx, program) with SMTLIBZ3QuantifiedTarget with TimeoutSolver)

      case "smt-cvc4" =>
        SolverFactory(() => new UnrollingSolver(ctx, program, new SMTLIBSolver(ctx, program) with SMTLIBCVC4Target) with TimeoutSolver)

      case "smt-2.5-cvc4" =>
        SolverFactory(() => new SMTLIBSolver(ctx, program) with SMTLIBUnrollingCVC4Target with TimeoutSolver)

      case _ =>
        ctx.reporter.fatalError("Unknown solver "+name)
    }

    val selectedSolvers = ctx.settings.selectedSolvers.map(getSolver)

    if (selectedSolvers.isEmpty) {
      ctx.reporter.fatalError("No solver selected. Aborting")
    } else if (selectedSolvers.size == 1) {
      selectedSolvers.head
    } else {
      SolverFactory( () => new PortfolioSolver(ctx, selectedSolvers.toSeq) with TimeoutSolver)
    }

  }

}
