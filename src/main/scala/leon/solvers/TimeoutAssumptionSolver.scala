/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers

import purescala.Trees.Expr

trait TimeoutAssumptionSolver extends TimeoutSolver with AssumptionSolver {

  abstract override def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
    optTimeout match {
      case Some(to) =>
        interruptAfter(to) {
          super.checkAssumptions(assumptions)
        }
      case None =>
        super.checkAssumptions(assumptions)
    }
  }
}

