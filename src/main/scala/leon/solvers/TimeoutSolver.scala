/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

import scala.sys.error

class TimeoutSolver(solver : Solver with  IncrementalSolverBuilder, timeoutMs : Long) extends Solver(solver.context) with IncrementalSolverBuilder {
  // I'm making this an inner class to fight the temptation of using it for anything meaningful.
  // We have Akka, these days, which whould be better in any respect for non-trivial things.
  private class Timer(onTimeout: => Unit) extends Thread {
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

    def halt : Unit = {
      keepRunning = false
    }
  }

  def withTimeout[T](solver: InterruptibleSolver)(body: => T): T = {
    val timer = new Timer(timeout(solver))
    timer.start
    val res = body
    timer.halt
    recoverFromTimeout(solver)
    res
  }

  var reachedTimeout = false
  def timeout(solver: InterruptibleSolver) {
    solver.halt
    reachedTimeout = true
  }

  def recoverFromTimeout(solver: InterruptibleSolver) {
    if (reachedTimeout) {
      solver.init
      reachedTimeout = false
    }
  }

  val description = solver.description + ", with timeout"
  val name = solver.name + "+to"

  override def setProgram(prog: Program): Unit = {
    solver.setProgram(prog)
  }

  def solve(expression: Expr) : Option[Boolean] = {
    withTimeout(solver) {
      solver.solve(expression)
    }
  }

  override def solveSAT(expression: Expr): (Option[Boolean], Map[Identifier, Expr]) = {
    withTimeout(solver) {
      solver.solveSAT(expression)
    }
  }

  override def solveSATWithCores(expression: Expr, assumptions: Set[Expr]): (Option[Boolean], Map[Identifier, Expr], Set[Expr]) = {
    withTimeout(solver) {
      solver.solveSATWithCores(expression, assumptions)
    }
  }

  def getNewSolver = new IncrementalSolver {
    val solver = TimeoutSolver.this.solver.getNewSolver

    def push(): Unit = {
      solver.push()
    }

    def pop(lvl: Int = 1): Unit = {
      solver.pop(lvl)
    }

    def assertCnstr(expression: Expr): Unit = {
      solver.assertCnstr(expression)
    }

    def halt(): Unit = {
      solver.halt()
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

  override def init() {
    solver.init
  }

  override def halt() {
    solver.halt
  }
}
