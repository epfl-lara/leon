/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package combinators

import scala.reflect.runtime.universe._

class PortfolioSolverFactory[S <: Solver](ctx: SolverContext, sfs: Seq[SolverFactory[S]])
  extends SolverFactory[PortfolioSolver[S] with TimeoutSolver] {

  def getNewSolver(): PortfolioSolver[S] with TimeoutSolver = {
    new PortfolioSolver[S](ctx, sfs.map(_.getNewSolver())) with TimeoutSolver
  }

  override def reclaim(s: Solver) = s match {
    case ps: PortfolioSolver[_] =>
      sfs.zip(ps.solvers).foreach { case (sf, s) =>
        sf.reclaim(s)
      }

    case _ =>
      ctx.context.reporter.error("Failed to reclaim a non-portfolio solver.")
  }

  val name = sfs.map(_.name).mkString("Pfolio(", ",", ")")
}

