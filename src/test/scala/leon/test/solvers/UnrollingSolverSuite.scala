/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test.solvers

import leon.test._
import leon.LeonContext
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.solvers._
import leon.solvers.z3._
import leon.solvers.combinators._

class UnrollingSolverSuite extends LeonSolverSuite {

  val sources = List(
    """|import leon.lang._
       |
       |object Minimal {
       |  def f(x: BigInt): BigInt = {
       |    if (x > 0) {
       |      x + f(x-1)
       |    } else {
       |      BigInt(1)
       |    }
       |  } ensuring { _ > 0 }
       |}""".stripMargin
  )

  def getSolver(implicit ctx: LeonContext, pgm: Program) = {
    new UnrollingSolver(ctx, pgm, new UninterpretedZ3Solver(ctx, pgm))
  }

  test("'true' should be valid") { implicit fix =>
    valid(BooleanLiteral(true))
  }

  test("'false' should be invalid") { implicit fix =>
    invalid(BooleanLiteral(false))
  }

  test("unrolling should enable recursive definition verification") { implicit fix =>
    val pgm = fix._2
    val fd = pgm.lookup("Minimal.f").collect {
      case fd: FunDef => fd
    }.get

    def f(e: Expr) = FunctionInvocation(fd.typed, Seq(e))
    val x = FreshIdentifier("x", IntegerType).toVariable

    valid(GreaterThan(f(x), InfiniteIntegerLiteral(0)))
  }
}
