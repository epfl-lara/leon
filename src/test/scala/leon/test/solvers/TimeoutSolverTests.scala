/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.solvers

import leon._
import leon.test._
import leon.utils.Interruptible
import leon.solvers._
import leon.solvers.combinators._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TypeTrees._

class TimeoutSolverTests extends LeonTestSuite {
  private class IdioticSolver(val context : LeonContext, val program: Program) extends Solver with Interruptible{
    val name = "Idiotic"
    val description = "Loops"

    var interrupted = false

    override def check: Option[Boolean] = {
      while(!interrupted) {
        Thread.sleep(100)
      }
      None
    }

    def recoverInterrupt() {
      interrupted = false
    }

    def interrupt() {
      interrupted = true
    }

    def assertCnstr(e: Expr) = {}

    def free() {}

    def getModel = ???
  }

  private def getTOSolver : SolverFactory[Solver] = {
    SolverFactory(() => (new IdioticSolver(testContext, Program.empty) with TimeoutSolver).setTimeout(1000L))
  }

  private def check(sf: SolverFactory[Solver], e: Expr): Option[Boolean] = {
    val s = sf.getNewSolver
    s.assertCnstr(e)
    s.check
  }

  test("TimeoutSolver 1") {
    val sf = getTOSolver
    assert(check(sf, BooleanLiteral(true)) === None)
    assert(check(sf, BooleanLiteral(false)) === None)

    val x = Variable(FreshIdentifier("x", IntegerType))
    assert(check(sf, Equals(x, x)) === None)
  }

  test("TimeoutSolver 2") {
    val sf = getTOSolver
    val x = Variable(FreshIdentifier("x", IntegerType))
    val o = InfiniteIntegerLiteral(1)
    assert(check(sf, Equals(Plus(x, o), Plus(o, x))) === None)
    assert(check(sf, Equals(Plus(x, o), x)) === None)
  }
}
