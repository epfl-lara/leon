/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers

import solvers.combinators._

import utils._
import purescala.Common._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.Trees._

trait SolverFactory[S <: Solver] extends Interruptible with LeonComponent {
  val context: LeonContext
  val program: Program

  def free() {}

  var interrupted = false

  override def interrupt() {
    interrupted = true 
  }

  override def recoverInterrupt() {
    interrupted = false
  }

  def getNewSolver(): S

  def withTimeout(ms: Long): TimeoutSolverFactory[S] = {
    this match {
      case tsf: TimeoutSolverFactory[S] =>
        // Unwrap/Rewrap to take only new timeout into account
        new TimeoutSolverFactory[S](tsf.sf, ms)
      case _ =>
        new TimeoutSolverFactory[S](this, ms)
    }
  }

  implicit val debugSection = DebugSectionSolver
}
