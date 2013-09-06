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

  def solverFactory: SolverFactory[Solver] = {
    new FairZ3SolverFactory(context, program)
  }

  def fastSolverFactory: SolverFactory[Solver] = {
    new UninterpretedZ3SolverFactory(context, program)
  }

}

object SynthesisContext {
  def fromSynthesizer(synth: Synthesizer) = {
    SynthesisContext(
      synth.context,
      synth.options,
      synth.functionContext,
      synth.program,
      synth.reporter)
  }
}

