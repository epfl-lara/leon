package leon
package solvers

trait InterruptibleSolver {
  def halt(): Unit
  def init(): Unit
}
