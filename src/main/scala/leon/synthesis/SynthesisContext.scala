package leon
package synthesis

import solvers.Solver

case class SynthesisContext(
  synth: Synthesizer,
  solver: Solver,
  simpleSolver: Solver,
  reporter: Reporter
)

object SynthesisContext {
  def fromSynthesizer(synth: Synthesizer) = SynthesisContext(synth, synth.solver, synth.solver, synth.reporter)
}

