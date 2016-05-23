/* Copyright 2009-2016 EPFL, Lausanne */

package leon.isabelle

import leon.regression.verification.VerificationSuite

class IsabelleVerificationSuite extends VerificationSuite {

  val testDir = "regression/verification/isabelle/"
  override val isabelle = true

  val optionVariants: List[List[String]] = List(List("--solvers=isabelle"))

}
