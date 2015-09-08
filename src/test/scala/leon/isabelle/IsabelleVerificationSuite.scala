package leon.isabelle

import leon._
import leon.regression.verification._
import leon.solvers.isabelle.AdaptationPhase
import leon.test._
import leon.verification.AnalysisPhase

class IsabelleVerificationSuite extends VerificationSuite {

  val testDir = "regression/verification/isabelle/"
  val pipeFront = xlang.NoXLangFeaturesChecking
  val pipeBack = AdaptationPhase andThen AnalysisPhase
  val optionVariants: List[List[String]] = List(List("--isabelle:download=true", "--solvers=isabelle"))

}
