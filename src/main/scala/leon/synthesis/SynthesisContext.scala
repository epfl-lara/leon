/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis

import solvers._
import solvers.combinators.PortfolioSolverSynth
import solvers.z3._
import purescala.Definitions.{Program, FunDef}

/**
 * This is global information per entire search, contains necessary information
 */
case class SynthesisContext(
  context: LeonContext,
  settings: SynthesisSettings,
  functionContext: FunDef,
  program: Program,
  reporter: Reporter
) {

  val rules = settings.rules

  val allSolvers: Map[String, SolverFactory[SynthesisContext.SynthesisSolver]] = Map(
    "fairz3" -> SolverFactory(() => new FairZ3Solver(context, program) with TimeoutAssumptionSolver),
    "enum"   -> SolverFactory(() => new EnumerationSolver(context, program) with TimeoutAssumptionSolver)
  )

  val solversToUse = allSolvers.filterKeys(settings.selectedSolvers)

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
      synth.settings,
      synth.ci.fd,
      synth.program,
      synth.reporter)
  }
}

