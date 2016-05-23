/* Copyright 2009-2016 EPFL, Lausanne */

package leon.integration.solvers

import leon._
import leon.test._
import leon.solvers._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.Types._

class TimeoutSolverSuite extends LeonTestSuite {
  private class IdioticSolver(val sctx: SolverContext, val program: Program) extends Solver with NaiveAssumptionSolver {
    val name = "Idiotic"
    val description = "Loops"

    var interrupted = false

    override def check: Option[Boolean] = {
      while(!interrupted) {
        Thread.sleep(50L)
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

    def push() {}
    def pop() {}

    def free() {}

    def reset() {}

    def getModel = ???
  }

  private def getTOSolver(ctx: LeonContext): SolverFactory[Solver] = {
    SolverFactory("idiotic", () => (new IdioticSolver(ctx.toSctx, Program.empty) with TimeoutSolver).setTimeout(200L))
  }

  private def check(sf: SolverFactory[Solver], e: Expr): Option[Boolean] = {
    val s = sf.getNewSolver()
    s.assertCnstr(e)
    s.check
  }

  test("TimeoutSolver 1") { ctx =>
    val sf = getTOSolver(ctx)
    assert(check(sf, BooleanLiteral(true)) === None)
    assert(check(sf, BooleanLiteral(false)) === None)

    val x = Variable(FreshIdentifier("x", IntegerType))
    assert(check(sf, Equals(x, x)) === None)

    sf.shutdown()
  }

  test("TimeoutSolver 2") { ctx =>
    val sf = getTOSolver(ctx)
    val x = Variable(FreshIdentifier("x", IntegerType))
    val o = InfiniteIntegerLiteral(1)
    assert(check(sf, Equals(Plus(x, o), Plus(o, x))) === None)
    assert(check(sf, Equals(Plus(x, o), x)) === None)

    sf.shutdown()
  }
}
