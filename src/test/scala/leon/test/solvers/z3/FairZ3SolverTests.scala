/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test.solvers.z3

import leon.LeonContext
import leon.SilentReporter

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._

import leon.solvers.Solver
import leon.solvers.z3.FairZ3Solver

import org.scalatest.FunSuite

class FairZ3SolverTests extends FunSuite {
  private var testCounter : Int = 0
  private def solverCheck(solver : Solver, expr : Expr, expected : Option[Boolean], msg : String) = {
    testCounter += 1

    test("Solver test #" + testCounter) {
      assert(solver.solve(expr) === expected, msg)
    }
  }

  private def assertValid(solver : Solver, expr : Expr) = solverCheck(
    solver, expr, Some(true),
    "Solver should prove the formula " + expr + " valid."
  )

  private def assertInvalid(solver : Solver, expr : Expr) = solverCheck(
    solver, expr, Some(false),
    "Solver should prove the formula " + expr + " invalid."
  )

  private def assertUnknown(solver : Solver, expr : Expr) = solverCheck(
    solver, expr, None,
    "Solver should not be able to decide the formula " + expr + "."
  )

  private val silentContext = LeonContext(reporter = new SilentReporter)

  // def f(fx : Int) : Int = fx + 1
  private val fx   : Identifier = FreshIdentifier("x").setType(Int32Type)
  private val fDef : FunDef = new FunDef(FreshIdentifier("f"), Int32Type, VarDecl(fx, Int32Type) :: Nil)
  fDef.body = Some(Plus(Variable(fx), IntLiteral(1)))

  private val minimalProgram = Program(
    FreshIdentifier("Minimal"), 
    ObjectDef(FreshIdentifier("Minimal"), Seq(
      fDef
    ), Seq.empty)
  )

  private val x : Expr = Variable(FreshIdentifier("x").setType(Int32Type))
  private val y : Expr = Variable(FreshIdentifier("y").setType(Int32Type))
  private def f(e : Expr) : Expr = FunctionInvocation(fDef, e :: Nil)

  private val solver = new FairZ3Solver(silentContext)
  solver.setProgram(minimalProgram)

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

  // This is true, and FairZ3Solver should know it (by inlining).
  private val unknown1 : Expr = Equals(f(x), Plus(x, IntLiteral(1)))
  assertValid(solver, unknown1)

  test("Check assumptions") {
    val b1 = Variable(FreshIdentifier("b").setType(BooleanType))
    val b2 = Variable(FreshIdentifier("b").setType(BooleanType))

    val f = And(b1, Not(b2))

    locally {
      val (result, model) = solver.solveSAT(f)
      assert(result === Some(true))
    }

    locally {
      val (result, model, core) = solver.solveSATWithCores(f, Set(b1))
      assert(result === Some(true))
      assert(core.isEmpty)
    }

    locally {
      val (result, model, core) = solver.solveSATWithCores(f, Set(b1, b2))
      assert(result === Some(false))
      assert(core === Set(b2))
    }
  }
}
