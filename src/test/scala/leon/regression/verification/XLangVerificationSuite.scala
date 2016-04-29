/* Copyright 2009-2016 EPFL, Lausanne */

package leon.regression.verification

import leon.solvers.SolverFactory

// If you add another regression test, make sure it contains exactly one object, whose name matches the file name.
// This is because we compile all tests from each folder together.
class XLangVerificationSuite extends VerificationSuite {

  val optionVariants: List[List[String]] = {
    val isZ3Available = SolverFactory.hasZ3

    (List(
      List(),
      List("--feelinglucky")
    ) ++ (
      if (isZ3Available)
        List(List("--solvers=smt-z3", "--feelinglucky"))
      else Nil
    )).map ("--timeout=300" :: _)
  }

  val testDir: String = "regression/verification/xlang/"
  override val desugarXLang = true
}

