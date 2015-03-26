/* Copyright 2009-2014 EPFL, Lausanne */

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
      new Z3Interpreter()
      true
    } catch {
      case e: java.io.IOException =>
        false
    }

    val isCVC4Available = try {
      new CVC4Interpreter()
      true
      // @EK: CVC4 works on most testcases already, but not all and thus cannot be used in regression.
    } catch {
      case e: java.io.IOException =>
        false
    }

    List(
      List("--feelinglucky"),
      List("--codegen", "--evalground", "--feelinglucky"),
      List("--solvers=fairz3,enum", "--codegen", "--evalground", "--feelinglucky")
    ) ++ (
      if (isZ3Available) List(List("--solvers=smt-z3", "--feelinglucky")) else Nil
    ) ++ (
      if (isCVC4Available) List(List("--solvers=smt-cvc4", "--feelinglucky")) else Nil
    )
  }
  
  forEachFileIn("valid") { output =>
    val Output(report, reporter) = output
    for (vc <- report.conditions) {
      if (vc.value != Some(true)) {
        fail("The following verification condition was invalid: " + vc.toString + " @" + vc.getPos)
      }
    }
    reporter.terminateIfError()
  }

  forEachFileIn("invalid") { output =>
    val Output(report, reporter) = output
    assert(report.totalInvalid > 0,
           "There should be at least one invalid verification condition.")
    assert(report.totalUnknown === 0,
           "There should not be unknown verification conditions.")
  }

}
