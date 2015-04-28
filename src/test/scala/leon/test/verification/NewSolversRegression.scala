/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.verification

import _root_.smtlib.interpreters._
import leon._
import leon.verification.AnalysisPhase

// If you add another regression test, make sure it contains one object whose name matches the file name
// This is because we compile all tests from each folder separately.

// This class is currently NOT in LeonAllTests
class NewSolversRegression extends VerificationRegression {
  
  val testDir = "regression/verification/newsolvers/"
  val pipeFront = xlang.NoXLangFeaturesChecking
  val pipeBack = AnalysisPhase
  val optionVariants: List[List[String]] = {
    val isZ3Available = try {
      Z3Interpreter.buildDefault
      true
    } catch {
      case e: java.io.IOException =>
        false
    }

    val isCVC4Available = try {
      CVC4Interpreter.buildDefault
      true
    } catch {
      case e: java.io.IOException =>
        false
    }

    (
      if (isZ3Available)
        List(List("--solvers=smt-z3-q", "--feelinglucky", "--timeout=3"))
      else Nil
    ) ++ (
      if (isCVC4Available)
        List(List("--solvers=smt-cvc4-proof", "--feelinglucky",  "--timeout=3"))
      else Nil
    )
  }
}
