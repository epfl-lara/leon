/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers

import scala.reflect.runtime.universe._

class TimeoutSolverFactory[+S <: TimeoutSolver : TypeTag](val sf: SolverFactory[S], to: Long) extends SolverFactory[S] {
  override def getNewSolver() = sf.getNewSolver().setTimeout(to)

  override val name = sf.name+" with t.o"

  override def reclaim(s: Solver) = sf.reclaim(s)

  override def shutdown() = sf.shutdown()
}

