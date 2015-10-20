package leon
package invariant.util

import utils._
import solvers._
import invariant.engine._
import purescala.Expressions._

object TimerUtil {
  /**
   * Timeout in milliseconds
   */
  def scheduleTask(callBack: () => Unit, timeOut: Long): Option[java.util.Timer] = {
    if (timeOut > 0) {
      val timer = new java.util.Timer();
      timer.schedule(new java.util.TimerTask() {
        def run() {
          callBack()
          timer.cancel() //the timer will be cancelled after it runs
        }
      }, timeOut);
      Some(timer)
    } else None
  }

  class InterruptOnSignal(it: Interruptible) {

    private class Poll(signal: => Boolean, onSignal: => Unit) extends Thread {
      private var keepRunning = true

      override def run(): Unit = {
        val startTime: Long = System.currentTimeMillis
        while (!signal && keepRunning) {
          Thread.sleep(100) // a relatively infrequent poll
        }
        if (signal && keepRunning) {
          onSignal
        }
      }

      def finishedRunning(): Unit = {
        keepRunning = false
      }
    }

    def interruptOnSignal[T](signal: => Boolean)(body: => T): T = {
      var recdSignal = false

      val timer = new Poll(signal, {
        it.interrupt()
        recdSignal = true
      })

      timer.start()
      val res = body
      timer.finishedRunning()

      if (recdSignal) {
        it.recoverInterrupt()
      }
      res
    }

  }

  class AbortableSolver(solverFactory: () => TimeoutSolver, ctx: InferenceContext) {

    def solveSAT(expr: Expr, timeout: Long): (Option[Boolean], Model) = {
      val solver = solverFactory()
      try {
        solver.setTimeout(timeout * 1000)
        solver.assertCnstr(expr)
        val res = new InterruptOnSignal(solver).interruptOnSignal(ctx.abort)(solver.check) match {
          case r @ Some(true) =>
            (r, solver.getModel)
          case r =>
            (r, Model.empty)
        }
        res
      } finally {
        solver.free()
      }
    }
  }
}