/* Copyright 2009-2016 EPFL, Lausanne */

package leon.regression.verification

import leon.solvers.SolverFactory

class OverflowVerificationSuite extends VerificationSuite {

  val optionVariants: List[List[String]] = {
    val isZ3Available = SolverFactory.hasZ3

    (List(
      List(),
      List("--feelinglucky")
    ) ++ (
      if (isZ3Available)
        List(List("--solvers=smt-z3", "--feelinglucky"))
      else Nil
    )).map ("--timeout=300" :: "--overflow" :: _)
  }

  val testDir: String = "regression/verification/overflow/"
}

