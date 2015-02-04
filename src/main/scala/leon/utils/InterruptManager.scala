/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package utils

import scala.collection.JavaConversions._

import java.util.concurrent.atomic.AtomicBoolean
import sun.misc.{Signal, SignalHandler}
import java.util.WeakHashMap

class InterruptManager(reporter: Reporter) extends Interruptible {
  private[this] val interruptibles = new WeakHashMap[Interruptible, Boolean]()
  private[this] val sigINT = new Signal("INT")
  private[this] var oldHandler: SignalHandler = null

  val interrupted: AtomicBoolean = new AtomicBoolean(false)

  @inline
  def isInterrupted() = interrupted.get()

  def interrupt() = synchronized {
    if (!interrupted.get()) {
      interrupted.set(true)

      val it = interruptibles.keySet.iterator
      for (i <- it) {
         i.interrupt()
      }
    } else {
      reporter.warning("Already interrupted!")
    }
  }

  def recoverInterrupt() = synchronized {
    if (interrupted.get()) {
      interrupted.set(false)

      val it = interruptibles.keySet.iterator
      for (i <- it) {
         i.recoverInterrupt()
      }
    } else {
      reporter.warning("Not interrupted!")
    }
  }

  def registerForInterrupts(i: Interruptible) = synchronized {
    if (interrupted.get) {
      i.interrupt()
    }
    interruptibles.put(i, true)
  }

  def registerSignalHandler() {
    oldHandler = Signal.handle(sigINT, new SignalHandler {
      def handle(sig: Signal) {
        Signal.handle(sigINT, oldHandler)
        println
        reporter.warning("Aborting Leon...")

        interrupt()

      }
    })
  }
}
