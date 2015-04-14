/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers

import purescala.Expressions.Expr

trait TimeoutAssumptionSolver extends TimeoutSolver with AssumptionSolver {

  abstract override def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
    optTimeout match {
      case Some(to) =>
        ti.interruptAfter(to) {
          super.checkAssumptions(assumptions)
        }
      case None =>
        super.checkAssumptions(assumptions)
    }
  }
}

