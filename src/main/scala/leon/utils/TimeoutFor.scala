/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package utils

class TimeoutFor(it: Interruptible) {
  private class Countdown(timeout: Long, onTimeout: => Unit) extends Thread {
    private var keepRunning = true
    override def run() : Unit = {
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

    def finishedRunning() : Unit = {
      keepRunning = false
    }
  }

  def interruptAfter[T](timeout: Long)(body: => T): T = {
    var reachedTimeout = false

    val timer = new Countdown(timeout, {
      it.interrupt()
      reachedTimeout = true
    })

    timer.start()
    val res = body
    timer.finishedRunning()

    if (reachedTimeout) {
      it.recoverInterrupt()
    }

    res
  }

  def interruptAfter[T](timeout: Option[Long])(body: => T): T = {
    timeout match {
      case Some(to) =>
        interruptAfter(to)(body)
      case None =>
        body
    }
  }
}
