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

  def newSolver: SynthesisContext.SynthesisSolver = {
    new FairZ3Solver(context, program)
  }

  def newFastSolver: SynthesisContext.SynthesisSolver = {
    new UninterpretedZ3Solver(context, program)
  }

  val solverFactory = SolverFactory(() => newSolver)
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

