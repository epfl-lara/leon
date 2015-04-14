/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package utils

import scala.collection.JavaConversions._

import java.util.concurrent.atomic.AtomicBoolean
import sun.misc.{Signal, SignalHandler}
import java.util.WeakHashMap

class InterruptManager(reporter: Reporter) extends Interruptible {
  private[this] val interruptibles = new WeakHashMap[Interruptible, Boolean]()
  private[this] val sigINT = new Signal("INT")
  private[this] val withinTimeout: AtomicBoolean = new AtomicBoolean(false)
  private[this] val handler = new SignalHandler {
    def handle(sig: Signal) {
      println()
      if (withinTimeout.get()) {
        reporter.warning("Aborting Leon...")
        System.exit(1)
      }
      else {
        reporter.warning("Interrupted...")
        setTimeout()
        interrupt()
      }
    }
  }
  private val exitWindow = 1000
  private[this] def setTimeout() = {
    import scala.concurrent.Future
    import scala.concurrent.ExecutionContext.Implicits.global
    withinTimeout.set(true)
    Future { Thread.sleep(exitWindow) } onComplete { _ => withinTimeout.set(false) }
    ()
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
