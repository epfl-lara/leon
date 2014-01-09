/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers

import purescala.Common._
import purescala.Trees._
import purescala.Definitions._

class SimpleSolverAPI(sf: SolverFactory[Solver]) {
  def solveVALID(expression: Expr, cond: Option[Expr]): Option[Boolean] = cond match {
    case Some(expr) => solveVALID(expression, expr)
    case None => solveVALID(expression)
  }

  def solveVALID(expression: Expr, cond: Expr = BooleanLiteral(true)): Option[Boolean] = {
    val s = sf.getNewSolver(cond)
    try {
      s.assertCnstr(Not(expression))
      s.check.map(r => !r)
    } finally {
      s.free()
    }
  }

  def solveSAT(expression: Expr, cond: Option[Expr]): (Option[Boolean], Map[Identifier, Expr]) = cond match {
    case Some(expr) => solveSAT(expression, expr)
    case None => solveSAT(expression)
  }

  def solveSAT(expression: Expr, cond: Expr = BooleanLiteral(true)): (Option[Boolean], Map[Identifier, Expr]) = {
    val s = sf.getNewSolver(cond)
    try {
      s.assertCnstr(expression)
      s.check match {
        case Some(true) =>
          (Some(true), s.getModel)
        case Some(false) =>
          (Some(false), Map())
        case None =>
          (None, Map())
      }
    } finally {
      s.free()
    }
  }
}

object SimpleSolverAPI {
  def apply(sf: SolverFactory[Solver]) = {
    new SimpleSolverAPI(sf)
  }

  // Wrapping an AssumptionSolver will automatically provide an extended
  // interface
  def apply(sf: SolverFactory[AssumptionSolver]) = {
    new SimpleAssumptionSolverAPI(sf)
  }
}
