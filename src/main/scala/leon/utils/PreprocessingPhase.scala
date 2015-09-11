/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package utils

import leon.xlang.XLangDesugaringPhase
import purescala.Definitions.Program

import leon.purescala._
import synthesis.{ConvertWithOracle, ConvertHoles}
import verification.InjectAsserts

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
      InliningPhase

    val pipeX = if(desugarXLang) {
      XLangDesugaringPhase andThen
      debugTrees("Program after xlang desugaring")
    } else {
      xlang.NoXLangFeaturesChecking
    }

    val phases =
      pipeBegin andThen
      pipeX     andThen
      new FunctionClosure andThen
      debugTrees("Program after pre-processing")

    phases.run(ctx)(p)
  }
}
