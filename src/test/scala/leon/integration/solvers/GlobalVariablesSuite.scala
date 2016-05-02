/* Copyright 2009-2016 EPFL, Lausanne */

package leon.integration.solvers

import leon.test._
import leon.test.helpers._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.ExprOps._
import leon.purescala.Constructors._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.LeonContext

import leon.solvers._
import leon.solvers.smtlib._
import leon.solvers.unrolling._
import leon.solvers.z3._

class GlobalVariablesSuite extends LeonTestSuiteWithProgram with ExpressionsDSL {

  val sources = List(
    """|import leon.lang._
       |import leon.annotation._
       |
       |object GlobalVariables {
       |
       |  def test(i: BigInt): BigInt = {
       |    0 // will be replaced
       |  }
       |} """.stripMargin
  )

  val solverNames: Seq[String] = {
    (if (SolverFactory.hasNativeZ3) Seq("fairz3") else Nil) ++
    (if (SolverFactory.hasZ3)       Seq("smt-z3") else Nil) ++
    (if (SolverFactory.hasCVC4)     Seq("smt-cvc4") else Nil)
  }

  // Check that we correctly extract several types from solver models
  for (sname <- solverNames) {
    test(s"Global Variables in $sname") { implicit fix =>
      val ctx = fix._1
      val pgm = fix._2

      pgm.lookup("GlobalVariables.test") match {
        case Some(fd: FunDef) =>
          val b0 = FreshIdentifier("B", BooleanType);
          fd.body = Some(IfExpr(b0.toVariable, bi(1), bi(-1)))

          val cnstr = LessThan(FunctionInvocation(fd.typed, Seq(bi(42))), bi(0))
          val solver = SolverFactory.getFromName(ctx, pgm)(sname).getNewSolver()
          solver.assertCnstr(And(b0.toVariable, cnstr))

          try { 
            if (solver.check != Some(false)) {
              fail("Global variables not correctly handled.")
            }
          } finally {
            solver.free()
          }
        case _ =>
          fail("Function with global body not found")
      }

    }
  }
}
