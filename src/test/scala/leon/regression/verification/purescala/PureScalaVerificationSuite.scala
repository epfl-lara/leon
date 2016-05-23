/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package regression.verification
package purescala

import leon.solvers.SolverFactory

// If you add another regression test, make sure it contains one object whose name matches the file name
// This is because we compile all tests from each folder together.
abstract class PureScalaVerificationSuite extends VerificationSuite {

  val testDir = "regression/verification/purescala/"

  val isZ3Available = SolverFactory.hasZ3

  val isCVC4Available = SolverFactory.hasCVC4

  val opts: List[List[String]] = {
    (List(
      List("--feelinglucky"),
      List("--codegen", /*"--evalground",*/ "--feelinglucky"),
      List("--solvers=fairz3,enum", "--codegen", /*"--evalground",*/ "--feelinglucky")) ++
      isZ3Available.option(List("--solvers=smt-z3", "--feelinglucky")) ++
      isCVC4Available.option(List("--solvers=smt-cvc4", "--feelinglucky")))
        .map( _ :+ "--timeout=300")
  }

}

trait PureScalaValidSuite extends PureScalaVerificationSuite {
  override def testAll() = testValid()
}

class PureScalaValidSuiteLuckyNativeZ3 extends PureScalaValidSuite {
  val optionVariants = List(opts(0))
}
class PureScalaValidSuiteCodeGenNativeZ3 extends PureScalaValidSuite {
  val optionVariants = List(opts(1))
}
class PureScalaValidSuiteEnumNativeZ3 extends PureScalaValidSuite {
  val optionVariants = List(opts(2))
  //override val ignored = Seq("valid/Predicate.scala","valid/TraceInductTacticTest.scala")
}
class PureScalaValidSuiteZ3 extends PureScalaValidSuite {
  val optionVariants = isZ3Available.option(opts(3)).toList
}
class PureScalaValidSuiteCVC4 extends PureScalaValidSuite {
  val optionVariants = isCVC4Available.option(opts.last).toList
}

trait PureScalaInvalidSuite extends PureScalaVerificationSuite {
  override def testAll() = testInvalid()
}

class PureScalaInvalidSuiteNativeZ3 extends PureScalaInvalidSuite {
  val optionVariants = opts.take(3)
}

class PureScalaInvalidSuiteZ3 extends PureScalaInvalidSuite {
  val optionVariants = isZ3Available.option(opts(3)).toList
}

class PureScalaInvalidSuiteCVC4 extends PureScalaInvalidSuite {
  val optionVariants = isCVC4Available.option(opts.last).toList
  override val ignored = List(
    "invalid/AbstractRefinementMap2.scala",
    "invalid/BinarySearchTreeQuant.scala",
    "invalid/PropositionalLogic.scala"
  )
}

