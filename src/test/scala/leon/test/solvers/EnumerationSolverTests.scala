/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test.solvers

import leon.test._
import leon.solvers._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.Types._

class EnumerationSolverTests extends LeonTestSuite {
  private def check(sf: SolverFactory[Solver], e: Expr): Option[Boolean] = {
    val s = sf.getNewSolver()
    s.assertCnstr(e)
    s.check
  }

  private def getSolver = {
    SolverFactory(() => new EnumerationSolver(testContext, Program.empty))
  }

  test("EnumerationSolver 1 (true)") {
    val sf = getSolver
    assert(check(sf, BooleanLiteral(true)) === Some(true))
  }

  test("EnumerationSolver 2 (x == 1)") {
    val sf = getSolver
    val x = Variable(FreshIdentifier("x", Int32Type))
    val o = IntLiteral(1)
    assert(check(sf, Equals(x, o)) === Some(true))
  }

  test("EnumerationSolver 3 (Limited range for ints)") {
    val sf = getSolver
    val x = Variable(FreshIdentifier("x", Int32Type))
    val o = IntLiteral(42)
    assert(check(sf, Equals(x, o)) === None)
  }
}
