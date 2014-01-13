/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis

import solvers._
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

  val solverFactory = FairZ3Solver.factory(context, program)
  val fastSolverFactory = SolverFactory(fd => new UninterpretedZ3Solver(context, program))

  def newSolver = solverFactory.getNewSolver(None)
  def newFastSolver = fastSolverFactory.getNewSolver(None)
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

