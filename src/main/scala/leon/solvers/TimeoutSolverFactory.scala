/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers

import purescala.Trees.{Expr => LeonExpr}

import scala.reflect.runtime.universe._

class TimeoutSolverFactory[+S <: TimeoutSolver : TypeTag](sf: SolverFactory[S], to: Long) extends SolverFactory[S] {
  override def getNewSolver(expr: LeonExpr) = sf.getNewSolver(expr).setTimeout(to)

  override val name = "SFact("+typeOf[S].toString+") with t.o"
}
