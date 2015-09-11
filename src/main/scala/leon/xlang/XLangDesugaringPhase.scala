/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package xlang

import purescala.Definitions.Program
import purescala.FunctionClosure

object XLangDesugaringPhase extends TransformationPhase {

  val name = "xlang desugaring"
  val description = "Desugar xlang features into PureScala"

  def apply(ctx: LeonContext, pgm: Program): Program = {
    val phases =
      ArrayTransformation andThen
      EpsilonElimination andThen
      ImperativeCodeElimination andThen
      (new FunctionClosure)
    phases.run(ctx)(pgm)
  }

}
