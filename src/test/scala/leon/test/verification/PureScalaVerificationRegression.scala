/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test.verification

import leon._
import leon.verification.AnalysisPhase

import _root_.smtlib.interpreters._

// If you add another regression test, make sure it contains one object whose name matches the file name
// This is because we compile all tests from each folder separately.
class PureScalaVerificationRegression extends VerificationRegression {
  
  val testDir = "regression/verification/purescala/"
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

    List(
      List("--feelinglucky"),
      List("--codegen", "--evalground", "--feelinglucky"),
      List("--solvers=fairz3,enum", "--codegen", "--evalground", "--feelinglucky")
    ) ++ (
      if (isZ3Available) List(
        List("--solvers=smt-z3", "--feelinglucky")
      ) else Nil
    ) ++ (
      if (isCVC4Available) List(
        List("--solvers=smt-cvc4", "--feelinglucky")
      ) else Nil
    )
  }

  test()

}
