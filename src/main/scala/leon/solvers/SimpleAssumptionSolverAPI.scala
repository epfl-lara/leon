/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers

import purescala.Common._
import purescala.Trees._

class SimpleAssumptionSolverAPI(sf: SolverFactory[AssumptionSolver]) extends SimpleSolverAPI(sf) {

  def solveSATWithCores(expression: Expr, assumptions: Set[Expr], cond: Option[Expr]):
      (Option[Boolean], Map[Identifier, Expr], Set[Expr]) = cond match {
    case Some(expr) => solveSATWithCores(expression, assumptions, expr)
    case None => solveSATWithCores(expression, assumptions)
  }

  def solveSATWithCores(expression: Expr, assumptions: Set[Expr], cond: Expr = BooleanLiteral(true)):
      (Option[Boolean], Map[Identifier, Expr], Set[Expr]) = {
    val s = sf.getNewSolver(cond)
    try {
      s.assertCnstr(expression)
      s.checkAssumptions(assumptions) match {
        case Some(true) =>
          (Some(true), s.getModel, Set())
        case Some(false) =>
          (Some(false), Map(), s.getUnsatCore)
        case None =>
          (None, Map(), Set())
      }
    } finally {
      s.free()
    }
  }
}
