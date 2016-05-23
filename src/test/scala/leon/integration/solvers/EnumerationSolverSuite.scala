/* Copyright 2009-2016 EPFL, Lausanne */

package leon.integration.solvers

import leon.solvers._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.LeonContext

class EnumerationSolverSuite extends LeonSolverSuite {
  def getSolver(implicit ctx: LeonContext, pgm: Program) = {
    new EnumerationSolver(ctx.toSctx, pgm)
  }

  val sources = Nil

  test("EnumerationSolver 1 (true)") { implicit fix =>
    sat(BooleanLiteral(true))
  }

  test("EnumerationSolver 2 (x == 1)") { implicit fix =>
    val x = FreshIdentifier("x", IntegerType).toVariable

    sat(Equals(x, InfiniteIntegerLiteral(0)))
  }
}
