/* Copyright 2009-2014 EPFL, Lausanne */

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

  val definedSolvers = Set("fairz3", "enum", "smt", "smt-z3", "smt-cvc4");

  def getFromSettings[S](ctx: LeonContext, program: Program): SolverFactory[TimeoutSolver] = {
    import combinators._
    import z3._
    import smtlib._

    def getSolver(name: String): SolverFactory[TimeoutSolver] = name match {
      case "fairz3" =>
        SolverFactory(() => new FairZ3Solver(ctx, program) with TimeoutSolver)

      case "enum"   =>
        SolverFactory(() => new EnumerationSolver(ctx, program) with TimeoutSolver)

      case "smt" | "smt-z3" =>
        val smtf = SolverFactory(() => new SMTLIBSolver(ctx, program) with SMTLIBZ3Target)
        SolverFactory(() => new UnrollingSolver(ctx, smtf) with TimeoutSolver)

      case "smt-cvc4" =>
        val smtf = SolverFactory(() => new SMTLIBSolver(ctx, program) with SMTLIBCVC4Target)
        SolverFactory(() => new UnrollingSolver(ctx, smtf) with TimeoutSolver)

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
