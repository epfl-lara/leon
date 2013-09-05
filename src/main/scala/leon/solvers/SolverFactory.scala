/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers

import utils._
import purescala.Common._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.Trees._

trait SolverFactory[S <: Solver] extends Interruptible with LeonComponent {
  val context: LeonContext
  val program: Program

  var freed = false
  val traceE = new Exception()

  override def finalize() {
    if (!freed) {
      //println("!! Solver not freed properly prior to GC:")
      //traceE.printStackTrace()
      free()
    }
  }

  def free() {
    freed = true
  }

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
}
