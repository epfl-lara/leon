/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package utils

import scala.collection.JavaConversions._

import java.util.concurrent.atomic.{AtomicLong, AtomicBoolean}
import sun.misc.{Signal, SignalHandler}
import java.util.WeakHashMap

class InterruptManager(reporter: Reporter) extends Interruptible {
  private[this] val interruptibles = new WeakHashMap[Interruptible, Boolean]()
  private[this] val sigINT = new Signal("INT")

  private[this] val lastTimestamp = new AtomicLong(0L)
  private val exitWindow = 1000L

  private[this] val handler = new SignalHandler {
    def handle(sig: Signal) {
      def now(): Long = System.currentTimeMillis()
      reporter.info("")
      if (now() - lastTimestamp.get < exitWindow) {
        reporter.warning("Aborting Leon...")
        System.exit(1)
      }
      else {
        reporter.warning("Interrupted...")
        lastTimestamp.set(now())
        interrupt()
      }
    }
  }

  val interrupted: AtomicBoolean = new AtomicBoolean(false)

  @inline
  def isInterrupted = interrupted.get

  def interrupt() = synchronized {
    if (!isInterrupted) {
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
    if (isInterrupted) {
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
    if (isInterrupted) {
      i.interrupt()
    }
    interruptibles.put(i, true)
  }

  // We should not need this because keys should automatically be removed
  // from the WeakHashMap when gc'ed.
  // But let's have it anyway!
  def unregisterForInterrupts(i: Interruptible) = synchronized {
    interruptibles.remove(i)
  }

  def registerSignalHandler() = Signal.handle(sigINT, handler)
}
