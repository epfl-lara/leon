/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers

import purescala.Expressions.Expr

trait AssumptionSolver extends Solver {
  def checkAssumptions(assumptions: Set[Expr]): Option[Boolean]
  def getUnsatCore: Set[Expr]
}
