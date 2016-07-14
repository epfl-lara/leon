/* Copyright 2009-2016 EPFL, Lausanne */

package leon.integration.solvers

import leon.LeonContext
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.solvers._

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
    SolverFactory.getFromName(ctx, pgm)("unrollz3").getNewSolver()
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
