/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis

import solvers.Solver
import purescala.Trees._
import purescala.Definitions.{Program, FunDef}
import purescala.Common.Identifier

import java.util.concurrent.atomic.AtomicBoolean

case class SynthesisContext(
  context: LeonContext,
  options: SynthesisOptions,
  functionContext: Option[FunDef],
  program: Program,
  solver: Solver,
  simpleSolver: Solver,
  reporter: Reporter,
  shouldStop: AtomicBoolean
)

object SynthesisContext {
  def fromSynthesizer(synth: Synthesizer) = {
    SynthesisContext(
      synth.context,
      synth.options,
      synth.functionContext,
      synth.program,
      synth.solver,
      synth.simpleSolver,
      synth.reporter,
      synth.shouldStop)
  }
}

