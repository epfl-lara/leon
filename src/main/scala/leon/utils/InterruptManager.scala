/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package utils

import scala.collection.JavaConversions._

import java.util.concurrent.atomic.AtomicBoolean
import sun.misc.{Signal, SignalHandler}
import java.util.WeakHashMap

class InterruptManager(reporter: Reporter) {
  private[this] val interruptibles = new WeakHashMap[Interruptible, Boolean]()
  private[this] val sigINT = new Signal("INT")
  private[this] var oldHandler: SignalHandler = null

  val interrupted: AtomicBoolean = new AtomicBoolean(false)

  @inline
  def isInterrupted() = interrupted.get()

  def interrupt() = synchronized {
    if (!interrupted.get()) {
      interrupted.set(true)

      interruptibles.keySet.foreach(_.interrupt())
    } else {
      reporter.warning("Already interrupted!")
    }
  }

  def recoverInterrupt() = synchronized {
    if (interrupted.get()) {
      interrupted.set(false)

      interruptibles.keySet.foreach(_.recoverInterrupt())
    } else {
      reporter.warning("Not interrupted!")
    }
  }

  def registerForInterrupts(i: Interruptible) {
    interruptibles.put(i, true)
  }

  def registerSignalHandler() {
    oldHandler = Signal.handle(sigINT, new SignalHandler {
      def handle(sig: Signal) {
        println
        reporter.info("Aborting...")

        interrupt()

        Signal.handle(sigINT, oldHandler)
      }
    })
  }
}
