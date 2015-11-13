/* Copyright 2009-2015 EPFL, Lausanne */

package leon.regression.verification

import smtlib.interpreters.Z3Interpreter

// If you add another regression test, make sure it contains exactly one object, whose name matches the file name.
// This is because we compile all tests from each folder together.
class XLangVerificationSuite extends VerificationSuite {

  val optionVariants: List[List[String]] = {
    val isZ3Available = try {
      Z3Interpreter.buildDefault.free()
      true
    } catch {
      case e: java.io.IOException =>
        false
    }

    List(
      List(),
      List("--feelinglucky")
    ) ++ (
      if (isZ3Available)
        List(List("--solvers=smt-z3", "--feelinglucky"))
      else Nil
    )
  }

  val testDir: String = "regression/verification/xlang/"
  override val desugarXLang = true
}
