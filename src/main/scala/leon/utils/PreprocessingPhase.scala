/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package utils

import leon.purescala._
import leon.purescala.Definitions.Program
import leon.solvers.isabelle.AdaptationPhase
import leon.verification.InjectAsserts
import leon.xlang.{NoXLangFeaturesChecking, XLangDesugaringPhase}

class PreprocessingPhase(desugarXLang: Boolean = false) extends LeonPhase[Program, Program] {

  val name = "preprocessing"
  val description = "Various preprocessings on Leon programs"

  override def run(ctx: LeonContext, p: Program): (LeonContext, Program) = {

    def debugTrees(title: String): LeonPhase[Program, Program] = {
      if (ctx.reporter.isDebugEnabled(DebugSectionTrees)) {
        PrintTreePhase(title)
      } else {
        NoopPhase[Program]()
      }
    }

    val checkX = if (desugarXLang) {
      NoopPhase[Program]()
    } else {
      NoXLangFeaturesChecking
    }

    val pipeBegin =
      debugTrees("Program after extraction") andThen
      checkX                                 andThen
      MethodLifting                          andThen
      TypingPhase                            andThen
      synthesis.ConversionPhase              andThen
      CheckADTFieldsTypes                    andThen
      ADTInvariants                          andThen
      InjectAsserts                          andThen
      InliningPhase

    val pipeX = if(desugarXLang) {
      XLangDesugaringPhase andThen
      debugTrees("Program after xlang desugaring")
    } else {
      NoopPhase[Program]()
    }

    val phases =
      pipeBegin andThen
      pipeX andThen
      FunctionClosure andThen
      AdaptationPhase andThen
      debugTrees("Program after pre-processing")

    phases.run(ctx, p)
  }
}
