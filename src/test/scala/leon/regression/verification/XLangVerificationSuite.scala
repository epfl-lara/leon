/* Copyright 2009-2015 EPFL, Lausanne */

package leon.regression.verification

class XLangVerificationSuite extends VerificationSuite {

  val optionVariants: List[List[String]] = List(
    List(),
    List("--feelinglucky"),
    List("--solvers=smt-z3", "--feelinglucky")
  )
  val testDir: String = "regression/verification/xlang/"
  override val desugarXLang = true
}
