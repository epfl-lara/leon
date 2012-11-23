package leon
package synthesis

import solvers.Solver

case class SynthesisContext(
  solver: Solver,
  reporter: Reporter
)

object SynthesisContext {
  def fromSynthesizer(synth: Synthesizer) = SynthesisContext(synth.solver, synth.reporter)
}

