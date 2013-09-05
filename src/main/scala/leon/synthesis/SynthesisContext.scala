/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis

import solvers._
import purescala.Trees._
import purescala.Definitions.{Program, FunDef}
import purescala.Common.Identifier

import java.util.concurrent.atomic.AtomicBoolean

case class SynthesisContext(
  context: LeonContext,
  options: SynthesisOptions,
  functionContext: Option[FunDef],
  program: Program,
  solverf: SolverFactory[Solver],
  fastSolverf: SolverFactory[Solver],
  reporter: Reporter
)

object SynthesisContext {
  def fromSynthesizer(synth: Synthesizer) = {
    SynthesisContext(
      synth.context,
      synth.options,
      synth.functionContext,
      synth.program,
      synth.solverf,
      synth.fastSolverf,
      synth.reporter)
  }
}

