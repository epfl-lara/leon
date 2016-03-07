/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package combinators

import scala.reflect.runtime.universe._

class PortfolioSolverFactory[S <: Solver](ctx: LeonContext, sfs: Seq[SolverFactory[S]])(implicit tag: TypeTag[S]) extends SolverFactory[PortfolioSolver[S] with TimeoutSolver] {

  def getNewSolver(): PortfolioSolver[S] with TimeoutSolver = {
    new PortfolioSolver[S](ctx, sfs.map(_.getNewSolver())) with TimeoutSolver
  }

  override def reclaim(s: Solver) = s match {
    case ps: PortfolioSolver[_] =>
      sfs.zip(ps.solvers).foreach { case (sf, s) =>
        sf.reclaim(s)
      }

    case _ =>
      ctx.reporter.error("Failed to reclaim a non-portfolio solver.")
  }
}

