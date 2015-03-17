/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers

import purescala.Common._
import purescala.Trees._

class SimpleAssumptionSolverAPI(sf: SolverFactory[AssumptionSolver]) extends SimpleSolverAPI(sf) {

  def solveSATWithCores(expression: Expr, assumptions: Set[Expr]): (Option[Boolean], Map[Identifier, Expr], Set[Expr]) = {
    val s = sf.getNewSolver()
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
