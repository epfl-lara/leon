/* Copyright 2009-2016 EPFL, Lausanne */

package leon.integration.purescala

import leon.test._

import leon._
import leon.solvers._
import leon.solvers.z3.UninterpretedZ3Solver
import leon.purescala.Definitions.Program
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.purescala.Common._
import leon.purescala.ExprOps

class SimplifyPathsSuite extends LeonTestSuite {
  val a = FreshIdentifier("a", BooleanType)
  val aV = a.toVariable
  val b = FreshIdentifier("b", BooleanType)
  val bV = b.toVariable
  val c = FreshIdentifier("c", BooleanType)
  val cV = b.toVariable

  val l1 = InfiniteIntegerLiteral(1)
  val l2 = InfiniteIntegerLiteral(2)

  def simplifyPaths(ctx: LeonContext, expr: Expr): Expr = {
    val uninterpretedZ3 = SolverFactory.getFromName(ctx, Program.empty)("nativez3-u")
    try {
      ExprOps.simplifyPaths(uninterpretedZ3)(expr)
    } finally {
      uninterpretedZ3.shutdown()
    }
  }

  test("Simplify Paths 01 - if(true)") { ctx => 
    val in  = IfExpr(BooleanLiteral(true), l1, l2)
    val exp = l1

    val out = simplifyPaths(ctx, in)
    assert(out === exp)
  }

  test("Simplify Paths 02 - expr match { .. }") { ctx => 
    val x = FreshIdentifier("x", BooleanType)
    val xV = x.toVariable

    val in  = MatchExpr(Equals(And(aV, Not(bV)), Not(Or(Not(aV), bV))), Seq(
      MatchCase(LiteralPattern(Some(x), BooleanLiteral(true)), None, And(xV, cV)),
      MatchCase(LiteralPattern(None, BooleanLiteral(false)), None, Not(cV))

    ))

    val out = simplifyPaths(ctx, in)
    assert(out.asInstanceOf[MatchExpr].cases.size == 1)
  }

  test("Simplify Paths 03 - ") { ctx =>
    val a = FreshIdentifier("a", IntegerType)
    val aV = a.toVariable
    val x = FreshIdentifier("x", IntegerType)
    val y = FreshIdentifier("y", IntegerType)
    val z = FreshIdentifier("y", IntegerType)
    val w = FreshIdentifier("y", IntegerType)
    val o = FreshIdentifier("o", IntegerType)

    val l0 = InfiniteIntegerLiteral(0)
    val l42 = InfiniteIntegerLiteral(42)

    val in  = MatchExpr(aV, Seq(
      MatchCase(LiteralPattern(None, l0), None, l0),
      MatchCase(WildcardPattern(Some(x)), Some(GreaterEquals(x.toVariable, l42)),   Plus(x.toVariable, l42)),
      MatchCase(WildcardPattern(Some(y)), Some(GreaterThan(y.toVariable, l42)),     Minus(x.toVariable, l42)),
      MatchCase(WildcardPattern(Some(z)), Some(GreaterThan(z.toVariable, l0)),      Plus(z.toVariable, l42)),
      MatchCase(WildcardPattern(Some(w)), Some(LessThan(w.toVariable, l0)),         Minus(w.toVariable, l42)),
      MatchCase(WildcardPattern(Some(o)), None,                                     InfiniteIntegerLiteral(1000))
    ))

    val exp  = MatchExpr(aV, Seq(
      MatchCase(LiteralPattern(None, l0), None, l0),
      MatchCase(WildcardPattern(Some(x)), Some(GreaterEquals(x.toVariable, l42)),   Plus(x.toVariable, l42)),
      MatchCase(WildcardPattern(Some(z)), Some(GreaterThan(z.toVariable, l0)),      Plus(z.toVariable, l42)),
      MatchCase(WildcardPattern(Some(w)), None,                                     Minus(w.toVariable, l42))
    ))

    val out = simplifyPaths(ctx, in)
    assert(out === exp)
  }

  test("Simplify Paths 04 - error - 1") { ctx =>
    val in = And(Error(BooleanType, ""), aV)
    val out = simplifyPaths(ctx, in)
    assert(out === in)
  }

  test("Simplify Paths 05 - error - 2") { ctx =>
    val in = And(BooleanLiteral(false), Error(BooleanType, ""))
    val out = simplifyPaths(ctx, in)
    assert(out === BooleanLiteral(false))
  }
}
