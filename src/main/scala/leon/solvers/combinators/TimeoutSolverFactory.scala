/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers
package combinators

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

import scala.sys.error

class TimeoutSolverFactory[S <: Solver](val sf: SolverFactory[S], val timeoutMs: Long) extends SolverFactory[Solver] {
  val description = sf.description + ", with "+timeoutMs+"ms timeout"
  val name = sf.name + "+to"

  val context = sf.context
  val program = sf.program

  private class Countdown(onTimeout: => Unit) extends Thread {
    private var keepRunning = true
    private val asMillis : Long = timeoutMs

    override def run : Unit = {
      val startTime : Long = System.currentTimeMillis
      var exceeded : Boolean = false

      while(!exceeded && keepRunning) {
        if(asMillis < (System.currentTimeMillis - startTime)) {
          exceeded = true
        }
        Thread.sleep(10)
      }
      if(exceeded && keepRunning) {
        onTimeout
      }
    }

    def finishedRunning : Unit = {
      keepRunning = false
    }
  }

  override def free() {
    sf.free()
  }

  def withTimeout[T](solver: S)(body: => T): T = {
    val timer = new Countdown(timeout(solver))
    timer.start
    val res = body
    timer.finishedRunning
    recoverFromTimeout(solver)
    res
  }

  var reachedTimeout = false
  def timeout(solver: S) {
    solver.interrupt()
    reachedTimeout = true
  }

  def recoverFromTimeout(solver: S) {
    if (reachedTimeout) {
      solver.recoverInterrupt()
      reachedTimeout = false
    }
  }

  def getNewSolver = new Solver {
    val solver = sf.getNewSolver

    def push(): Unit = {
      solver.push()
    }

    def pop(lvl: Int = 1): Unit = {
      solver.pop(lvl)
    }

    def assertCnstr(expression: Expr): Unit = {
      solver.assertCnstr(expression)
    }

    def interrupt() {
      solver.interrupt()
    }

    def recoverInterrupt() {
      solver.recoverInterrupt()
    }

    def check: Option[Boolean] = {
      withTimeout(solver){
        solver.check
      }
    }

    def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
      withTimeout(solver){
        solver.checkAssumptions(assumptions)
      }
    }

    def getModel: Map[Identifier, Expr] = {
      solver.getModel
    }

    def getUnsatCore: Set[Expr] = {
      solver.getUnsatCore
    }
  }
}
