/* Copyright 2009-2016 EPFL, Lausanne */

package leon.integration.solvers

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.LeonContext

import leon.solvers.z3._

class FairZ3SolverTests extends LeonSolverSuite {

  val sources = List(
    """|import leon.lang._
       |
       |object Minimal {
       |  def f(x: BigInt) = x + 1
       |}""".stripMargin
   )

  def getSolver(implicit ctx: LeonContext, pgm: Program) = {
    new FairZ3Solver(ctx.toSctx, pgm)
  }

  test("Tautology 1") { implicit fix =>
    valid(BooleanLiteral(true))
  }

  test("Tautology 2") { implicit fix =>
    val x = FreshIdentifier("x", IntegerType).toVariable
    valid(Equals(Plus(x, x), Times(InfiniteIntegerLiteral(2), x)))
  }

  // This one contains a function invocation but is valid regardless of its
  // interpretation, so should be proved anyway.
  test("Tautology 3") { implicit fix =>
    val pgm = fix._2
    val fd = pgm.lookup("Minimal.f").collect {
      case fd: FunDef => fd
    }.get

    def f(e: Expr) = FunctionInvocation(fd.typed, Seq(e))
    val x = FreshIdentifier("x", IntegerType).toVariable
    val y = FreshIdentifier("y", IntegerType).toVariable

    valid(Implies(Not(Equals(f(x), f(y))), Not(Equals(x, y))))
  }

  test("Wrong 1") { implicit fix =>
    invalid(BooleanLiteral(false))
  }

  test("Wrong 2") { implicit fix =>
    val x = FreshIdentifier("x", IntegerType).toVariable
    unsat(And(GreaterThan(x, InfiniteIntegerLiteral(0)), Equals(Plus(x, x), Times(InfiniteIntegerLiteral(3), x))))
  }

  test("Correct after unfolding") { implicit fix =>
    val pgm = fix._2
    val fd = pgm.lookup("Minimal.f").collect {
      case fd: FunDef => fd
    }.get

    def f(e: Expr) = FunctionInvocation(fd.typed, Seq(e))
    val x = FreshIdentifier("x", IntegerType).toVariable

    valid(Equals(f(x), Plus(x, InfiniteIntegerLiteral(1))))
  }
}
