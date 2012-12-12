package leon
package solvers

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

import scala.sys.error

class TimeoutSolver(solver : Solver, timeout : Int) extends Solver(solver.context) with NaiveIncrementalSolver {
  // I'm making this an inner class to fight the temptation of using it for anything meaningful.
  // We have Akka, these days, which whould be better in any respect for non-trivial things.
  private class Timer(callback : () => Unit, maxSecs : Int) extends Thread {
    private var keepRunning = true
    private val asMillis : Long = 1000L * maxSecs
  
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
        callback()
      }
    }
  
    def halt : Unit = {
      keepRunning = false
    }
  }

  val description = solver.description + ", with timeout"
  val name = solver.name + "+to"

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
