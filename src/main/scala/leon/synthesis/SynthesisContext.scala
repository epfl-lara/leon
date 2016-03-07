/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis

import solvers._
import purescala.Definitions.{Program, FunDef}
import evaluators._

/**
 * This is global information per entire search, contains necessary information
 */
class SynthesisContext(
  context: LeonContext,
  val settings: SynthesisSettings,
  val functionContext: FunDef,
  val program: Program
) extends LeonContext(
    context.reporter,
    context.interruptManager,
    context.options,
    context.files,
    context.classDir,
    context.timers
) {

  val solverFactory = SolverFactory.getFromSettings(context, program)

  lazy val defaultEvaluator = {
    new DefaultEvaluator(context, program)
  }

}
