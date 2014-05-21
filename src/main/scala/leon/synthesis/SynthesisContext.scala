/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import solvers._
import solvers.combinators.PortfolioSolverSynth
import solvers.z3._

import purescala.Trees._
import purescala.Definitions.{Program, FunDef}
import purescala.Common.Identifier

import java.util.concurrent.atomic.AtomicBoolean

case class SynthesisContext(
  context: LeonContext,
  options: SynthesisOptions,
  functionContext: Option[FunDef],
  program: Program,
  reporter: Reporter
) {

  val rules = options.rules

  val allSolvers: Map[String, SolverFactory[SynthesisContext.SynthesisSolver]] = Map(
    "fairz3" -> SolverFactory(() => new FairZ3Solver(context, program) with TimeoutAssumptionSolver),
    "enum"   -> SolverFactory(() => new EnumerationSolver(context, program) with TimeoutAssumptionSolver)
  )

  val solversToUse = allSolvers.filterKeys(options.selectedSolvers)

  val solverFactory: SolverFactory[SynthesisContext.SynthesisSolver] = if (solversToUse.isEmpty) {
    reporter.fatalError("No solver selected. Aborting")
  } else if (solversToUse.size == 1) {
    solversToUse.values.head
  } else {
    SolverFactory( () => new PortfolioSolverSynth(context, solversToUse.values.toSeq) with TimeoutAssumptionSolver)
  }

  def newSolver: SynthesisContext.SynthesisSolver = {
    solverFactory.getNewSolver()
  }

  def newFastSolver: SynthesisContext.SynthesisSolver = {
    new UninterpretedZ3Solver(context, program) with TimeoutAssumptionSolver
  }

  val fastSolverFactory = SolverFactory(() => newFastSolver)

}

object SynthesisContext {
  type SynthesisSolver = TimeoutAssumptionSolver with IncrementalSolver

  def fromSynthesizer(synth: Synthesizer) = {
    SynthesisContext(
      synth.context,
      synth.options,
      synth.functionContext,
      synth.program,
      synth.reporter)
  }
}

