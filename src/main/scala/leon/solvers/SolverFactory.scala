/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers

import scala.reflect.runtime.universe._

abstract class SolverFactory[+S <: Solver : TypeTag] {
  def getNewSolver(): S

  val name = "SFact("+typeOf[S].toString+")"
}

object SolverFactory {
  def apply[S <: Solver : TypeTag](builder: () => S): SolverFactory[S] = {
    new SolverFactory[S] {
      def getNewSolver() = builder()
    }
  }
}
