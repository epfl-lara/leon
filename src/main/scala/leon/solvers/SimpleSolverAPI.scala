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
      sf.reclaim(s)
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
      sf.reclaim(s)
    }
  }

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
      sf.reclaim(s)
    }
  }
}

object SimpleSolverAPI {
  def apply(sf: SolverFactory[Solver]) = {
    new SimpleSolverAPI(sf)
  }
}
