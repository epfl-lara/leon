/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test
package solvers

import leon._
import leon.solvers._
import leon.solvers.combinators._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TypeTrees._

class TimeoutSolverTests extends LeonTestSuite {
  private class IdioticSolver(val context : LeonContext, val program: Program) extends SolverFactory[Solver] {
    enclosing =>

    val name = "Idiotic"
    val description = "Loops"

    def getNewSolver = new Solver {
      def check = {
        while(!interrupted) {
          Thread.sleep(100)
        }
        None
      }

      def assertCnstr(e: Expr) {}

      def checkAssumptions(assump: Set[Expr]) = ???
      def getModel = ???
      def getUnsatCore = ???
      def push() = ???
      def pop(lvl: Int) = ???

      def interrupt() = enclosing.interrupt()
      def recoverInterrupt() = enclosing.recoverInterrupt()
    }
  }

  private def getTOSolver : TimeoutSolverFactory[Solver] = {
    new IdioticSolver(testContext, Program.empty).withTimeout(1000L)
  }

  private def check(sf: TimeoutSolverFactory[Solver], e: Expr): Option[Boolean] = {
    val s = sf.getNewSolver
    s.assertCnstr(e)
    s.check
  }

  test("TimeoutSolver 1") {
    val sf = getTOSolver
    assert(check(sf, BooleanLiteral(true)) === None)
    assert(check(sf, BooleanLiteral(false)) === None)

    val x = Variable(FreshIdentifier("x").setType(Int32Type))
    assert(check(sf, Equals(x, x)) === None)
  }

  test("TimeoutSolver 2") {
    val sf = getTOSolver
    val x = Variable(FreshIdentifier("x").setType(Int32Type))
    val o = IntLiteral(1)
    assert(check(sf, Equals(Plus(x, o), Plus(o, x))) === None)
    assert(check(sf, Equals(Plus(x, o), x)) === None)
  }
}
