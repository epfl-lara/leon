/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package utils

import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.ScopeSimplifier
import purescala.Path
import solvers._

object Simplifiers {
  
  def bestEffort(ctx: LeonContext, p: Program)(e: Expr, pc: Path = Path.empty): Expr = {
    val solverf = SolverFactory.uninterpreted(ctx, p)

    try {
      val simplifiers = (simplifyLets _).
        andThen(simplifyPaths(solverf, pc)).
        andThen(simplifyArithmetic).
        andThen(evalGround(ctx, p)).
        andThen(normalizeExpression)

      // Simplify first using stable simplifiers
      val s = fixpoint(simplifiers, 5)(e)

      // Clean up ids/names
      (new ScopeSimplifier).transform(s)
    } finally {
      solverf.shutdown()
    }
  }

  def namePreservingBestEffort(ctx: LeonContext, p: Program)(e: Expr): Expr = {
    val solverf = SolverFactory.uninterpreted(ctx, p)

    try { 
      val simplifiers = (simplifyArithmetic _).
        andThen(evalGround(ctx, p)).
        andThen(normalizeExpression)

      // Simplify first using stable simplifiers
      fixpoint(simplifiers, 5)(e)
    } finally {
      solverf.shutdown()
    }
  }
}
