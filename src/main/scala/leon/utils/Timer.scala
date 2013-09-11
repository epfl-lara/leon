/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package utils

class TimerCollection(val name: String) {
  var min: Long = 0L
  var tot: Long = 0L
  var max: Long = 0L
  var n: Int = 0

  def +=(sw: Timer) = synchronized { 
    val ms = sw.getMillis
    if(n == 0 || ms < min) {
      min = ms
    }
    if(n == 0 || ms > max) {
      max = ms
    }
    n   += 1
    tot += ms
  }

  override def toString = {
    if (n == 0) {
      "%-30s    N/A".format(name+":")
    } else if (n > 1) {
      "%-30s %6d ms (min: %d, avg: %d, max: %d, n: %d)".format(name+":", tot, min, tot/n, max, n)
    } else {
      "%-30s %6d ms".format(name+":", tot)
    }
  }

  def getMillis = tot
}

/** Implements a timer for profiling purposes */
class Timer(name: String = "Timer") {
  var beginning: Long = 0L
  var end: Long = 0L
  var acc: Long = 0L

  def start: this.type = {
    beginning = System.currentTimeMillis
    end       = 0L
    this
  }

  def restart: this.type = { 
    beginning = 0L
    end = 0L
    acc = 0L

    start
  }

  def stop {
    end        = System.currentTimeMillis
    acc       += (end - beginning)
    beginning  = 0L
  }

  def getMillis: Long = {
    if (isRunning) {
      acc + (System.currentTimeMillis-beginning)
    } else {
      acc
    }
  }

  def isRunning = beginning != 0L

  override def toString = "%20s: %5d%sms".format(name, getMillis, if (isRunning) "..." else "")
}

class TimerCollections {
  private var all = Map[String, TimerCollection]()

  def get(name: String): TimerCollection = all.getOrElse(name, {
    val sw = new TimerCollection(name)
    all += name -> sw
    sw
  })

  def add(swc: TimerCollection) {
    all += swc.name -> swc
  }

  def getAll = all
}
