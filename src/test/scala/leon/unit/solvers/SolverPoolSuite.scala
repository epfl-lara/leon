/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.solvers

import leon._
import leon.test._
import leon.solvers._
import leon.solvers.combinators._

import leon.purescala.Definitions._
import leon.purescala.Expressions._

class SolverPoolSuite extends LeonTestSuite {

  private class DummySolver(val sctx: SolverContext, val program: Program) extends Solver with NaiveAssumptionSolver {
    val name = "Dummy"
    val description = "dummy"

    def check: Option[Boolean] = None
    def assertCnstr(e: Expr) = {}
    def free() {}
    def reset() {}
    def getModel = ???
    def push() {}
    def pop() {}
    def interrupt() {}
    def recoverInterrupt() {}
  }

  def sfactory(implicit ctx: LeonContext): SolverFactory[Solver] = {
    SolverFactory("dummy", () => new DummySolver(ctx.toSctx, Program.empty))
  }

  val poolSize = 5;

  test(s"SolverPool has at least $poolSize solvers") { implicit ctx =>

    val sp = new SolverPoolFactory(ctx, sfactory)

    var solvers = Set[Solver]()

    for (i <- 1 to poolSize) {
      solvers += sp.getNewSolver()
    }

    solvers.size === poolSize
  }

  test("SolverPool reuses solvers") { implicit ctx =>

    val sp = new SolverPoolFactory(ctx, sfactory)

    var solvers = Set[Solver]()

    for (i <- 1 to poolSize) {
      val s = sp.getNewSolver()
      solvers += s
      sp.reclaim(s)
    }

    for (i <- 1 to poolSize) {
      val s = sp.getNewSolver()
      assert(solvers contains s, "Solver not reused?")
      sp.reclaim(s)
    }
  }

  test(s"SolverPool can grow") { implicit ctx =>

    val sp = new SolverPoolFactory(ctx, sfactory)

    var solvers = Set[Solver]()

    for (i <- 1 to poolSize+3) {
      solvers += sp.getNewSolver()
    }

    solvers.size === poolSize+3
  }
}
