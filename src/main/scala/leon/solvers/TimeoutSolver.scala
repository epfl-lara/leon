package leon
package solvers

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

import scala.sys.error

class TimeoutSolver(solver : Solver, timeout : Int) extends Solver(solver.reporter) {

  val description = solver.description + ", with timeout"
  override val shortDescription = solver.shortDescription + "+t"

  override def setProgram(prog: Program): Unit = {
    solver.setProgram(prog)
  }

  def solve(expression: Expr) : Option[Boolean] = {
    val timer = new Timer(() => solver.halt, timeout)
    timer.start
    val res = solver.solve(expression)
    timer.halt
    res
  }

  override def init() {
    solver.init
  }
  override def halt() {
    solver.halt
  }

}
