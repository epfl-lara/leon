/* Copyright 2009-2015 EPFL, Lausanne */

package leon.integration.solvers

import leon.test._
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.Constructors._
import leon.purescala.Types._
import leon.LeonContext
import leon.LeonOption

import leon.solvers._
import leon.solvers.smtlib._
import leon.solvers.cvc4._
import leon.solvers.z3._

class QuantifierSolverSuite extends LeonTestSuiteWithProgram {

  val sources = List()

  override val leonOpts = List("--checkmodels")

  val solverNames: Seq[String] = {
    (if (SolverFactory.hasNativeZ3) Seq("fairz3") else Nil) ++
    (if (SolverFactory.hasZ3)       Seq("smt-z3") else Nil) ++
    (if (SolverFactory.hasCVC4)     Seq("smt-cvc4") else Nil)
  }

  val f1: Identifier = FreshIdentifier("f1", FunctionType(Seq(IntegerType, IntegerType), IntegerType))
  val A = TypeParameter.fresh("A")
  val f2: Identifier = FreshIdentifier("f2", FunctionType(Seq(A, A), A))

  def app(f: Expr, args: Expr*): Expr = Application(f, args)
  def bi(i: Int): Expr = InfiniteIntegerLiteral(i)

  def associative(f: Expr): Expr = {
    val FunctionType(Seq(t1, t2), _) = f.getType
    assert(t1 == t2, "Can't specify associativity for type " + f.getType)

    val ids @ Seq(x, y, z) = Seq("x", "y", "z").map(name => FreshIdentifier(name, t1, true))
    Forall(ids.map(ValDef(_)), Equals(
      app(f, app(f, Variable(x), Variable(y)), Variable(z)),
      app(f, Variable(x), app(f, Variable(y), Variable(z)))))
  }

  def commutative(f: Expr): Expr = {
    val FunctionType(Seq(t1, t2), _) = f.getType
    assert(t1 == t2, "Can't specify commutativity for type " + f.getType)

    val ids @ Seq(x, y) = Seq("x", "y").map(name => FreshIdentifier(name, t1, true))
    Forall(ids.map(ValDef(_)), Equals(
      app(f, Variable(x), Variable(y)), app(f, Variable(y), Variable(x))))
  }

  def idempotent(f: Expr): Expr = {
    val FunctionType(Seq(t1, t2), _) = f.getType
    assert(t1 == t2, "Can't specify idempotency for type " + f.getType)

    val ids @ Seq(x, y, z) = Seq("x", "y", "z").map(name => FreshIdentifier(name, t1, true))
    Forall(ids.map(ValDef(_)), Equals(
      app(f, Variable(x), Variable(y)),
      app(f, Variable(x), app(f, Variable(x), Variable(y)))))
  }

  def rotative(f: Expr): Expr = {
    val FunctionType(Seq(t1, t2), _) = f.getType
    assert(t1 == t2, "Can't specify associativity for type " + f.getType)

    val ids @ Seq(x, y, z) = Seq("x", "y", "z").map(name => FreshIdentifier(name, t1, true))
    Forall(ids.map(ValDef(_)), Equals(
      app(f, app(f, Variable(x), Variable(y)), Variable(z)),
      app(f, app(f, Variable(y), Variable(z)), Variable(x))))
  }

  val satisfiable = List(
    "paper 1"                -> and(associative(Variable(f1)),
      Not(Equals(app(Variable(f1), app(Variable(f1), bi(1), bi(2)), bi(3)),
      app(Variable(f1), bi(1), app(Variable(f1), bi(2), bi(2)))))),
    "paper 2"                -> and(commutative(Variable(f1)), idempotent(Variable(f1)),
      Not(Equals(app(Variable(f1), app(Variable(f1), bi(1), bi(2)), bi(2)),
      app(Variable(f1), bi(1), app(Variable(f1), bi(2), app(Variable(f1), bi(1), bi(3))))))),
    "assoc not comm int"     -> and(associative(Variable(f1)), Not(commutative(Variable(f1)))),
    "assoc not comm generic" -> and(associative(Variable(f2)), Not(commutative(Variable(f2)))),
    "comm not assoc int"     -> and(commutative(Variable(f1)), Not(associative(Variable(f1)))),
    "comm not assoc generic" -> and(commutative(Variable(f2)), Not(associative(Variable(f2))))
  )

  val unification: Expr = {
    val ids @ Seq(x, y) = Seq("x", "y").map(name => FreshIdentifier(name, IntegerType, true))
    Forall(ids.map(ValDef(_)), Not(Equals(app(Variable(f1), Variable(x), Variable(y)), app(Variable(f1), Variable(y), Variable(x)))))
  }

  val unsatisfiable = List(
    "comm + rotate = assoc int"     -> and(commutative(Variable(f1)), rotative(Variable(f1)), Not(associative(Variable(f1)))),
    "comm + rotate = assoc generic" -> and(commutative(Variable(f2)), rotative(Variable(f2)), Not(associative(Variable(f2)))),
    "unification"                   -> unification
  )

  def checkSolver(solver: Solver, expr: Expr, sat: Boolean)(implicit fix: (LeonContext, Program)): Unit = {
    try {
      solver.assertCnstr(expr)
      solver.check match {
        case Some(true) if sat && fix._1.reporter.warningCount > 0 =>
          fail(s"Solver $solver - Constraint ${expr.asString} doesn't guarantee model validity!?")
        case Some(true) if sat => // checkmodels ensures validity
        case Some(false) if !sat => // we were looking for unsat
        case res => fail(s"Solver $solver - Constraint ${expr.asString} has result $res!?")
      }
    } finally {
      solver.free()
    }
  }

  for (sname <- solverNames; (ename, expr) <- satisfiable) {
    test(s"Satisfiable quantified formula $ename in $sname") { implicit fix =>
      val (ctx, pgm) = fix
      val solver = SolverFactory.getFromName(ctx, pgm)(sname).getNewSolver()
      checkSolver(solver, expr, true)
    }

    /*
    test(s"Satisfiable quantified formula $ename in $sname with partial models") { implicit fix =>
      val (ctx, pgm) = fix
      val newCtx = ctx.copy(options = ctx.options.filter(_ != UnrollingProcedure.optPartialModels) :+
        LeonOption(UnrollingProcedure.optPartialModels)(true))
      val solver = sf(newCtx, pgm)
      checkSolver(solver, expr, true)
    }
    */
  }

  for (sname <- solverNames; (ename, expr) <- unsatisfiable) {
    test(s"Unsatisfiable quantified formula $ename in $sname") { implicit fix =>
      val (ctx, pgm) = fix
      val solver = SolverFactory.getFromName(ctx, pgm)(sname).getNewSolver()
      checkSolver(solver, expr, false)
    }
  }
}
