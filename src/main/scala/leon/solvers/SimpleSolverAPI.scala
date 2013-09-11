/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers

import purescala.Common._
import purescala.Trees._

case class SimpleSolverAPI(sf: SolverFactory[Solver]) {
  def solveVALID(expression: Expr): Option[Boolean] = {
    val s = sf.getNewSolver()
    s.assertCnstr(Not(expression))
    s.check.map(r => !r)
  }

  def free() {
    sf.free()
  }

  def solveSAT(expression: Expr): (Option[Boolean], Map[Identifier, Expr]) = {
    val s = sf.getNewSolver()
    s.assertCnstr(expression)
    s.check match {
      case Some(true) =>
        (Some(true), s.getModel)
      case Some(false) =>
        (Some(false), Map())
      case None =>
        (None, Map())
    }
  }

  def solveSATWithCores(expression: Expr, assumptions: Set[Expr]): (Option[Boolean], Map[Identifier, Expr], Set[Expr]) = {
    val s = sf.getNewSolver()
    s.assertCnstr(expression)
    s.checkAssumptions(assumptions) match {
      case Some(true) =>
        (Some(true), s.getModel, Set())
      case Some(false) =>
        (Some(false), Map(), s.getUnsatCore)
      case None =>
        (None, Map(), Set())
    }
  }
}

