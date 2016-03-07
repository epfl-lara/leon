/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers

import purescala.Expressions._

class SimpleSolverAPI(sf: SolverFactory[Solver]) {
  def solveVALID(expression: Expr): Option[Boolean] = {
    val s = sf.getNewSolver()
    try {
      s.assertCnstr(Not(expression))
      s.check.map(r => !r)
    } finally {
      sf.reclaim(s)
    }
  }

  def solveSAT(expression: Expr): (Option[Boolean], Model) = {
    val s = sf.getNewSolver()
    try {
      s.assertCnstr(expression)
      s.check match {
        case Some(true) =>
          (Some(true), s.getModel)
        case Some(false) =>
          (Some(false), Model.empty)
        case None =>
          (None, Model.empty)
      }
    } finally {
      sf.reclaim(s)
    }
  }

  def solveSATWithCores(expression: Expr, assumptions: Set[Expr]): Option[Either[Set[Expr], Model]] = {
    val s = sf.getNewSolver()
    try {
      s.assertCnstr(expression)
      s.checkAssumptions(assumptions) match {
        case Some(false) =>
          Some(Left(s.getUnsatCore))
        case Some(true) =>
          Some(Right(s.getModel))
        case None =>
          None
      }
    } finally {
      sf.reclaim(s)
    }
  }
}

object SimpleSolverAPI {
  def apply(sf: SolverFactory[Solver]) = {
    new SimpleSolverAPI(sf)
  }
}
