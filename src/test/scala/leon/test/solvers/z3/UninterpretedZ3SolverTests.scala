/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test
package solvers.z3

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
  private val fx   : Identifier = FreshIdentifier("x").setType(Int32Type)
  private val fDef : FunDef = new FunDef(FreshIdentifier("f"), Int32Type, VarDecl(fx, Int32Type) :: Nil)
  fDef.body = Some(Plus(Variable(fx), IntLiteral(1)))

  // g is a function that is not in the program (on purpose)
  private val gDef : FunDef = new FunDef(FreshIdentifier("g"), Int32Type, VarDecl(fx, Int32Type) :: Nil)
  gDef.body = Some(Plus(Variable(fx), IntLiteral(1)))

  private val minimalProgram = Program(
    FreshIdentifier("Minimal"), 
    ObjectDef(FreshIdentifier("Minimal"), Seq(
      fDef
    ), Seq.empty)
  )

  private val x : Expr = Variable(FreshIdentifier("x").setType(Int32Type))
  private val y : Expr = Variable(FreshIdentifier("y").setType(Int32Type))
  private def f(e : Expr) : Expr = FunctionInvocation(fDef, e :: Nil)
  private def g(e : Expr) : Expr = FunctionInvocation(gDef, e :: Nil)

  private val solver = SimpleSolverAPI(new UninterpretedZ3SolverFactory(testContext, minimalProgram))

  private val tautology1 : Expr = BooleanLiteral(true)
  assertValid(solver, tautology1)

  private val tautology2 : Expr = Equals(Plus(x, x), Times(IntLiteral(2), x))
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

  private val wrong2 : Expr = Equals(Plus(x, x), Times(IntLiteral(3), x))
  assertInvalid(solver, wrong2)

  // This is true, but that solver shouldn't know it.
  private val unknown1 : Expr = Equals(f(x), Plus(x, IntLiteral(1)))
  assertUnknown(solver, unknown1)

  test("Expected crash on undefined functions.") {
    intercept[Exception] {
      solver.solveVALID(Equals(g(x), g(x)))
    }
  }

  solver.free()
}
