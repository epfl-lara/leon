/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers

import scala.reflect.runtime.universe._

class TimeoutSolverFactory[+S <: TimeoutSolver : TypeTag](sf: SolverFactory[S], to: Long) extends SolverFactory[S] {
  override def getNewSolver() = sf.getNewSolver().setTimeout(to)

  override val name = "SFact("+typeOf[S].toString+") with t.o"
}

