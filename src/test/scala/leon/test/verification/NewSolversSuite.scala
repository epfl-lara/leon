/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.verification

import _root_.smtlib.interpreters._
import leon._
import leon.verification.AnalysisPhase

// If you add another regression test, make sure it contains one object whose name matches the file name
// This is because we compile all tests from each folder separately.

// This class is currently NOT in LeonAllTests
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

    if (isCVC4Available)
      List(List("--solvers=smt-cvc4-cex,smt-cvc4-proof,ground", "--feelinglucky", "--timeout=5"))
    else Nil

  }
}
