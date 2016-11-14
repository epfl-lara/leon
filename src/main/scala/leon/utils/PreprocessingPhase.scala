/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package utils

import leon.purescala._
import leon.purescala.Definitions.Program
import leon.solvers.isabelle.AdaptationPhase
import leon.verification.InjectAsserts
import leon.xlang.{NoXLangFeaturesChecking, XLangDesugaringPhase, XLangCleanupPhase}

class PreprocessingPhase(genc: Boolean = false) extends LeonPhase[Program, Program] {

  val name = "preprocessing"
  val description = "Various preprocessings on Leon programs"

  override def run(ctx: LeonContext, p: Program): (LeonContext, Program) = {

    def debugTrees(title: String) =
      PrintTreePhase(title).when(ctx.reporter.isDebugEnabled(DebugSectionTrees))

    val pipeBegin =
      debugTrees("Program after extraction")      andThen
      MethodLifting                               andThen
      TypingPhase                                 andThen
      xlang.EffectsChecking                       andThen
      synthesis.ConversionPhase

    val pipeBeginWithInlining =
      if(ctx.findOptionOrDefault(Main.MainComponent.optLazyEval)) {
        // here disable inlining
        pipeBegin
      } else pipeBegin andThen InliningPhase

    // Do not desugar xlang when generating C code
    val pipeX = (
      XLangDesugaringPhase andThen
      debugTrees("Program after xlang desugaring")
    ) when (!genc)

    def pipeEnd = (
      InjectAsserts  andThen
      FunctionClosure andThen
      //XLangCleanupPhase andThen
      AdaptationPhase
    ) when (!genc)

    val phases =
      pipeBeginWithInlining andThen
      pipeX andThen
      pipeEnd andThen
      debugTrees("Program after pre-processing")

    phases.run(ctx, p)
  }
}
