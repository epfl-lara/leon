/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers

import purescala.Common._
import purescala.Expressions._

class SimpleSolverAPI(sf: SolverFactory[Solver]) {
  def solveVALID(expression: Expr): Option[Boolean] = {
    val s = sf.getNewSolver()
    try {
      s.assertCnstr(Not(expression))
      s.check.map(r => !r)
    } finally {
      s.free()
    }
  }

  def solveSAT(expression: Expr): (Option[Boolean], Map[Identifier, Expr]) = {
    val s = sf.getNewSolver()
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
