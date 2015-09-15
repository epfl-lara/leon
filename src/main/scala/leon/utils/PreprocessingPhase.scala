/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package utils

import leon.purescala._
import leon.purescala.Definitions.Program
import leon.purescala.Quantification.CheckForalls
import leon.solvers.isabelle.AdaptationPhase
import leon.synthesis.{ConvertWithOracle, ConvertHoles}
import leon.verification.InjectAsserts
import leon.xlang.XLangDesugaringPhase

class PreprocessingPhase(private val desugarXLang: Boolean = false) extends TransformationPhase {

  val name = "preprocessing"
  val description = "Various preprocessings on Leon programs"

  def apply(ctx: LeonContext, p: Program): Program = {

    def debugTrees(title: String): LeonPhase[Program, Program] = {
      if (ctx.reporter.isDebugEnabled(DebugSectionTrees)) {
        PrintTreePhase(title)
      } else {
        NoopPhase[Program]()
      }
    }

    val pipeBegin =
      debugTrees("Program after extraction") andThen
      MethodLifting                          andThen
      TypingPhase                            andThen
      ConvertWithOracle                      andThen
      ConvertHoles                           andThen
      CompleteAbstractDefinitions            andThen
      CheckADTFieldsTypes                    andThen
      InjectAsserts                          andThen
      InliningPhase                          andThen
      CheckForalls

    val pipeX = if(desugarXLang) {
      XLangDesugaringPhase andThen
      debugTrees("Program after xlang desugaring")
    } else {
      xlang.NoXLangFeaturesChecking
    }

    val phases =
      pipeBegin andThen
      pipeX andThen
      new FunctionClosure andThen
      AdaptationPhase andThen
      debugTrees("Program after pre-processing")

    phases.run(ctx)(p)
  }
}
