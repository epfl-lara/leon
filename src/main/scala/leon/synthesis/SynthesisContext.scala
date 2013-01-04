package leon
package synthesis

import solvers.Solver
import purescala.Trees._
import purescala.Definitions.{Program, FunDef}
import purescala.Common.Identifier

import java.util.concurrent.atomic.AtomicBoolean

case class SynthesisContext(
  options: SynthesizerOptions,
  functionContext: Option[FunDef],
  program: Program,
  solver: Solver,
  reporter: Reporter,
  shouldStop: AtomicBoolean
)

object SynthesisContext {
  def fromSynthesizer(synth: Synthesizer) = {
    SynthesisContext(
      synth.options,
      synth.functionContext,
      synth.program,
      synth.solver,
      synth.reporter,
      new AtomicBoolean(false))
  }
}

