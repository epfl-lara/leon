/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package utils

import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.ScopeSimplifier
import solvers.z3.UninterpretedZ3Solver
import solvers._

object Simplifiers {
  
  def bestEffort(ctx: LeonContext, p: Program)(e: Expr): Expr = {
    val uninterpretedZ3 = SolverFactory(() => new UninterpretedZ3Solver(ctx, p))

    val simplifiers = List[Expr => Expr](
      simplifyTautologies(uninterpretedZ3)(_),
      simplifyLets,
      simplifyPaths(uninterpretedZ3)(_),
      simplifyArithmetic,
      evalGround(ctx, p),
      normalizeExpression
    )

    val simple = { expr: Expr =>
      simplifiers.foldLeft(expr){ case (x, sim) => 
        sim(x)
      }
    }

    // Simplify first using stable simplifiers
    val s = fixpoint(simple, 5)(e)

    // Clean up ids/names
    (new ScopeSimplifier).transform(s)
  }

  def namePreservingBestEffort(ctx: LeonContext, p: Program)(e: Expr): Expr = {
    val uninterpretedZ3 = SolverFactory(() => new UninterpretedZ3Solver(ctx, p))

    val simplifiers = List[Expr => Expr](
      simplifyTautologies(uninterpretedZ3)(_),
      simplifyArithmetic,
      evalGround(ctx, p),
      normalizeExpression
    )

    val simple = { expr: Expr =>
      simplifiers.foldLeft(expr){ case (x, sim) => 
        sim(x)
      }
    }

    // Simplify first using stable simplifiers
    fixpoint(simple, 5)(e)
  }
}
