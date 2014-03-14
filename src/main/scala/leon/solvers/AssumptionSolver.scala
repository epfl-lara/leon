/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers

import purescala.Trees.Expr

trait AssumptionSolver extends Solver {
  def checkAssumptions(assumptions: Set[Expr]): Option[Boolean]
  def getUnsatCore: Set[Expr]
}
