/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.util

import utils._

object TimerUtil {
  /**
   * Timeout in milliseconds
   */
  def scheduleTask(callBack: () => Unit, timeOut: Long): Option[java.util.Timer] = {
    if (timeOut > 0) {
      val timer = new java.util.Timer()
      timer.schedule(new java.util.TimerTask() {
        def run() {
          callBack()
          timer.cancel() //the timer will be cancelled after it runs
        }
      }, timeOut)
      Some(timer)
    } else None
  }
}

class InterruptOnSignal(it: Interruptible) {

  private class Poll(signal: => Boolean, onSignal: => Unit) extends Thread {
    private var keepRunning = true

    override def run(): Unit = {
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