/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers

import utils._

trait TimeoutSolver extends Solver with Interruptible {

  private class Countdown(timeout: Long, onTimeout: => Unit) extends Thread {
    private var keepRunning = true
    override def run : Unit = {
      val startTime : Long = System.currentTimeMillis
      var exceeded : Boolean = false

      while(!exceeded && keepRunning) {
        if(timeout < (System.currentTimeMillis - startTime)) {
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

  protected var optTimeout: Option[Long] = None;
  protected def interruptAfter[T](timeout: Long)(body: => T): T = {
    var reachedTimeout = false

    val timer = new Countdown(timeout, {
      interrupt()
      reachedTimeout = true
    })

    timer.start
    val res = body
    timer.finishedRunning

    if (reachedTimeout) {
      recoverInterrupt()
    }

    res
  }

  def setTimeout(timeout: Long): this.type = {
    optTimeout = Some(timeout)
    this
  }

  abstract override def check: Option[Boolean] = {
    optTimeout match {
      case Some(to) =>
        interruptAfter(to) {
          super.check
        }
      case None =>
        super.check
    }
  }

}
