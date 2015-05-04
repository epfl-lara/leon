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
  program: Program
) {

  val reporter = context.reporter

  val rules = settings.rules

  val solverFactory = SolverFactory.getFromSettings(context, program)

  def newSolver = {
    solverFactory.getNewSolver()
  }

  val fastSolverFactory = SolverFactory.uninterpreted(context, program)

  def newFastSolver = {
    fastSolverFactory.getNewSolver()
  }
}

object SynthesisContext {

  def fromSynthesizer(synth: Synthesizer) = {
    SynthesisContext(
      synth.context,
      synth.settings,
      synth.ci.fd,
      synth.program
    )
  }
}
