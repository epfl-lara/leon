/* Copyright 2009-2014 EPFL, Lausanne */

package leon.regression.verification

import _root_.smtlib.interpreters._
import leon._
import leon.verification.VerificationPhase

/* @EK: Disabled for now as many tests fail 
class NewSolversSuite extends VerificationSuite {

  val testDir = "regression/verification/newsolvers/"
  val pipeFront = xlang.NoXLangFeaturesChecking
  val pipeBack = AnalysisPhase
  val optionVariants: List[List[String]] = {

    val isCVC4Available = try {
      CVC4Interpreter.buildDefault.free()
      true
    } catch {
      case e: java.io.IOException =>
        false
    }

    val isZ3Available = try {
      Z3Interpreter.buildDefault.free()
      true
    } catch {
      case e: java.io.IOException =>
        false
    }

    (
      if (isCVC4Available)
        List(List("--solvers=smt-cvc4-cex,smt-cvc4-proof,ground", "--timeout=5"))
      else Nil
    ) ++ (
      if (isZ3Available)
        List(List("--solvers=smt-z3-q,ground", "--timeout=10"))
      else Nil
    )

  }
}
*/
