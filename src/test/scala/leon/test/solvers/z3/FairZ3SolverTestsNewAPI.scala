/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test.solvers.z3

import leon.test._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._

import leon.solvers._
import leon.solvers.z3._

class FairZ3SolverTestsNewAPI extends LeonTestSuite {
  private var testCounter : Int = 0
  private def solverCheck(solver : SolverFactory[Solver], expr : Expr, expected : Option[Boolean], msg : String) = {
    testCounter += 1

    test("Solver test #" + testCounter) {
      val sub = solver.getNewSolver

      try {
        sub.assertCnstr(Not(expr))

        assert(sub.check === expected.map(!_), msg)
      } finally {
        sub.free()
      }
    }
  }

  private def assertValid(solver : SolverFactory[Solver], expr : Expr) = solverCheck(
    solver, expr, Some(true),
    "Solver should prove the formula " + expr + " valid."
  )

  private def assertInvalid(solver : SolverFactory[Solver], expr : Expr) = solverCheck(
    solver, expr, Some(false),
    "Solver should prove the formula " + expr + " invalid."
  )

  private def assertUnknown(solver : SolverFactory[Solver], expr : Expr) = solverCheck(
    solver, expr, None,
    "Solver should not be able to decide the formula " + expr + "."
  )

  // def f(fx : Int) : Int = fx + 1
  private val fx   : Identifier = FreshIdentifier("x", IntegerType)
  private val fDef : FunDef = new FunDef(FreshIdentifier("f"), Nil, IntegerType, ValDef(fx) :: Nil, DefType.MethodDef)
  fDef.body = Some(Plus(Variable(fx), InfiniteIntegerLiteral(1)))

  private val minimalProgram = Program(
    FreshIdentifier("Minimal"), 
    List(UnitDef(
        FreshIdentifier("Minimal"),
        List(ModuleDef(FreshIdentifier("Minimal"), Seq(fDef), false)
    )))
  )

  private val x : Expr = Variable(FreshIdentifier("x", IntegerType))
  private val y : Expr = Variable(FreshIdentifier("y", IntegerType))
  private def f(e : Expr) : Expr = FunctionInvocation(fDef.typed, e :: Nil)

  private val solver = SolverFactory(() => new FairZ3Solver(testContext, minimalProgram))

  private val tautology1 : Expr = BooleanLiteral(true)
  assertValid(solver, tautology1)

  private val tautology2 : Expr = Equals(Plus(x, x), Times(InfiniteIntegerLiteral(2), x))
  assertValid(solver, tautology2)

  // This one contains a function invocation but is valid regardless of its
  // interpretation, so should be proved anyway.
  private val tautology3 : Expr = Implies(
    Not(Equals(f(x), f(y))),
    Not(Equals(x, y))
  )
  assertValid(solver, tautology3)

  private val wrong1 : Expr = BooleanLiteral(false)
  assertInvalid(solver, wrong1)

  private val wrong2 : Expr = Equals(Plus(x, x), Times(InfiniteIntegerLiteral(3), x))
  assertInvalid(solver, wrong2)

  // This is true, and FairZ3Solver should know it (by inlining).
  private val unknown1 : Expr = Equals(f(x), Plus(x, InfiniteIntegerLiteral(1)))
  assertValid(solver, unknown1)

  test("Check assumptions") {
    val b1 = Variable(FreshIdentifier("b", BooleanType))
    val b2 = Variable(FreshIdentifier("b", BooleanType))

    val f = And(b1, Not(b2))

    locally {
      val sub = solver.getNewSolver
      try {
        sub.assertCnstr(f)
        assert(sub.check === Some(true))
      } finally {
        sub.free()
      }
    }

    locally {
      val sub = solver.getNewSolver
      try {
        sub.assertCnstr(f)
        val result = sub.checkAssumptions(Set(b1))

        assert(result === Some(true))
        assert(sub.getUnsatCore.isEmpty)
      } finally {
        sub.free()
      }
    }

    locally {
      val sub = solver.getNewSolver
      try {
        sub.assertCnstr(f)

        val result = sub.checkAssumptions(Set(b1, b2))
        assert(result === Some(false))
        assert(sub.getUnsatCore === Set(b2))
      } finally {
        sub.free()
      }
    }
  }
}
