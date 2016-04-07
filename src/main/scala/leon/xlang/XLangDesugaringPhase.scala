/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package xlang

import utils._
import purescala.Definitions.Program

object XLangDesugaringPhase extends LeonPhase[Program, Program] {

  val name = "xlang desugaring"
  val description = "Desugar xlang features into PureScala"

  override def run(ctx: LeonContext, pgm: Program): (LeonContext, Program) = {

    def debugTrees(title: String) =
      PrintTreePhase(title).when(ctx.reporter.isDebugEnabled(DebugSectionTrees))

    val phases =
      debugTrees("Program before starting xlang-desugaring") andThen
      IntroduceGlobalStatePhase andThen
      debugTrees("Program after introduce-global-state") andThen
      AntiAliasingPhase andThen
      debugTrees("Program after anti-aliasing") andThen
      EpsilonElimination andThen
      ImperativeCodeElimination

    phases.run(ctx, pgm)
  }

}
