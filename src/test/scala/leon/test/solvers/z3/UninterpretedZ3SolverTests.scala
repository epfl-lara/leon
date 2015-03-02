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

class UninterpretedZ3SolverTests extends LeonTestSuite {
  private var testCounter : Int = 0
  private def solverCheck(solver : SimpleSolverAPI, expr : Expr, expected : Option[Boolean], msg : String) = {
    testCounter += 1

    test("Solver test #" + testCounter) {
      assert(solver.solveVALID(expr) === expected, msg)
    }
  }

  private def assertValid(solver : SimpleSolverAPI, expr : Expr) = solverCheck(
    solver, expr, Some(true),
    "Solver should prove the formula " + expr + " valid."
  )

  private def assertInvalid(solver : SimpleSolverAPI, expr : Expr) = solverCheck(
    solver, expr, Some(false),
    "Solver should prove the formula " + expr + " invalid."
  )

  private def assertUnknown(solver : SimpleSolverAPI, expr : Expr) = solverCheck(
    solver, expr, None,
    "Solver should not be able to decide the formula " + expr + "."
  )

  // def f(fx : Int) : Int = fx + 1
  private val fx   : Identifier = FreshIdentifier("x", IntegerType)
  private val fDef : FunDef = new FunDef(FreshIdentifier("f"), Nil, IntegerType, ValDef(fx) :: Nil, DefType.MethodDef)
  fDef.body = Some(Plus(Variable(fx), InfiniteIntegerLiteral(1)))

  // g is a function that is not in the program (on purpose)
  private val gDef : FunDef = new FunDef(FreshIdentifier("g"), Nil, IntegerType, ValDef(fx) :: Nil, DefType.MethodDef)
  gDef.body = Some(Plus(Variable(fx), InfiniteIntegerLiteral(1)))

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
  private def g(e : Expr) : Expr = FunctionInvocation(gDef.typed, e :: Nil)

  private val solver = SimpleSolverAPI(SolverFactory(() => new UninterpretedZ3Solver(testContext, minimalProgram)))

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

  // This is true, but that solver shouldn't know it.
  // However, since the uninterpreted solver is a nice backend for the unrolling solver,
  // it makes more sense to allow such formulas even if they are not completely known
  /*
  private val unknown1 : Expr = Equals(f(x), Plus(x, InfiniteIntegerLiteral(1)))
  assertUnknown(solver, unknown1)
  */

  assertValid(solver, Equals(g(x), g(x)))
}
