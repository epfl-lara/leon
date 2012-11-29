package leon
package solvers

import purescala.Common._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.Trees._

trait IncrementalSolverBuilder {
  def getNewSolver: IncrementalSolver
}

trait IncrementalSolver {
  // New Solver API
  // Moslty for z3 solvers since z3 4.3

  def push(): Unit
  def pop(lvl: Int = 1): Unit
  def assertCnstr(expression: Expr): Unit

  def check: Option[Boolean]
  def checkAssumptions(assumptions: Set[Expr]): Option[Boolean]
  def getModel: Map[Identifier, Expr]
  def getUnsatCore: Set[Expr]
}

trait NaiveIncrementalSolver extends IncrementalSolverBuilder {
  def solveSAT(e: Expr): (Option[Boolean], Map[Identifier, Expr])

  def getNewSolver = new IncrementalSolver {
    private var stack = List[List[Expr]]()

    def push() {
      stack = Nil :: stack
    }

    def pop(lvl: Int = 1) {
      stack = stack.drop(lvl)
    }

    def assertCnstr(expression: Expr) {
      stack = (expression :: stack.head) :: stack.tail
    }

    private def allConstraints() = stack.flatten

    private var unsatCore = Set[Expr]()

    def check: Option[Boolean] = {
      solveSAT(And(allConstraints()))._1
    }

    def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
      solveSAT(And((assumptions  ++ allConstraints()).toSeq))._1 match {
        case Some(true) =>
          unsatCore = Set[Expr]()
          Some(true)
        case r =>
          unsatCore = assumptions.toSet
          r
      }
    }

    def getModel: Map[Identifier, Expr] = {
      Map[Identifier, Expr]()
    }

    def getUnsatCore: Set[Expr] = {
      unsatCore
    }
  }
}
