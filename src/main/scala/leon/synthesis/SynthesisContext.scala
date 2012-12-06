package leon
package synthesis

import solvers.Solver

import java.util.concurrent.atomic.AtomicBoolean

case class SynthesisContext(
  solver: Solver,
  reporter: Reporter,
  shouldStop: AtomicBoolean
)

object SynthesisContext {
  def fromSynthesizer(synth: Synthesizer) = SynthesisContext(synth.solver, synth.reporter, new AtomicBoolean(false))
}

