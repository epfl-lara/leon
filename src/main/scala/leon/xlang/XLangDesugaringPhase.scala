/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package xlang

import purescala.Definitions.Program

object XLangDesugaringPhase extends LeonPhase[Program, Program] {

  val name = "xlang desugaring"
  val description = "Desugar xlang features into PureScala"

  override def run(ctx: LeonContext, pgm: Program): (LeonContext, Program) = {
    val phases =
      //ArrayTransformation andThen
      AntiAliasingPhase andThen
      EpsilonElimination andThen
      ImperativeCodeElimination

    phases.run(ctx, pgm)
  }

}
