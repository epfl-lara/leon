/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers

import purescala.Trees.{Expr => LeonExpr, BooleanLiteral}

import scala.reflect.runtime.universe._

abstract class SolverFactory[+S <: Solver : TypeTag] {

  def getNewSolver: S = getNewSolver(BooleanLiteral(true))

  def getNewSolver(cond: Option[LeonExpr]): S = cond match {
    case Some(expr) => getNewSolver(expr)
    case None => getNewSolver
  }

  def getNewSolver(cond: LeonExpr): S

  val name = "SFact("+typeOf[S].toString+")"
}

object SolverFactory {
  def apply[S <: Solver : TypeTag](builder: (LeonExpr => S)): SolverFactory[S] = {
    new SolverFactory[S] {
      def getNewSolver(cond: LeonExpr) = builder(cond)
    }
  }

  def apply[S <: TimeoutSolver : TypeTag](builder: (LeonExpr => S), timeout: Long): SolverFactory[S] = {
    new SolverFactory[S] {
      def getNewSolver(cond: LeonExpr) = builder(cond).setTimeout(timeout)
    }
  }
}
