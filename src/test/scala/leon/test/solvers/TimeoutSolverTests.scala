/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test.solvers

import org.scalatest.FunSuite

import leon._
import leon.solvers._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TypeTrees._

class TimeoutSolverTests extends FunSuite {
  private class IdioticSolver(ctx : LeonContext) extends Solver(ctx) with NaiveIncrementalSolver {
    val name = "Idiotic"
    val description = "Loops when it doesn't know"

    def solve(expression : Expr) : Option[Boolean] = expression match {
      case BooleanLiteral(true)  => Some(true)
      case BooleanLiteral(false) => Some(false)
      case Equals(x, y) if x == y => Some(true)
      case _ => 
        while(!forceStop) {
          Thread.sleep(1)
        }
        None
    }
  }

  private def getTOSolver : Solver = {
    val s = new TimeoutSolver(new IdioticSolver(LeonContext()), 1000L)
    s.setProgram(Program.empty)
    s
  }

  test("TimeoutSolver 1") {
    val s = getTOSolver
    assert(s.solve(BooleanLiteral(true)) === Some(true))
    assert(s.solve(BooleanLiteral(false)) === Some(false))

    val x = Variable(FreshIdentifier("x").setType(Int32Type))
    assert(s.solve(Equals(x, x)) === Some(true))
  }

  test("TimeoutSolver 2") {
    val s = getTOSolver
    val x = Variable(FreshIdentifier("x").setType(Int32Type))
    val o = IntLiteral(1)
    assert(s.solve(Equals(Plus(x, o), Plus(o, x))) === None)
    assert(s.solve(Equals(Plus(x, o), x)) === None)
  }
}
