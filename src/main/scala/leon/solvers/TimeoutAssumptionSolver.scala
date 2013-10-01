/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers

import purescala.Trees.Expr

trait TimeoutAssumptionSolver extends TimeoutSolver with AssumptionSolver {

  protected def innerCheckAssumptions(assumptions: Set[Expr]): Option[Boolean]

  override def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
    optTimeout match {
      case Some(to) =>
        interruptAfter(to) {
          innerCheckAssumptions(assumptions)
        }
      case None =>
        innerCheckAssumptions(assumptions)
    }
  }
}

