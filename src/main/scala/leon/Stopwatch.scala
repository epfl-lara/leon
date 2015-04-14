/* Copyright 2009-2015 EPFL, Lausanne */

package leon

class StopwatchCollection(name: String) {
  var acc: Long = 0L
  
  var stopwatches = List[Stopwatch]()

  def +=(sw: Stopwatch) = synchronized { acc += sw.getMillis }

  def getMillis = {
    val running =
	    (0L /: stopwatches) {
	      (res, sw) => res + sw.getMillis
	    }
      
    acc + running
  }
  
  def newStopwatch = {
    val result = new Stopwatch()
    stopwatches :+= result
    result
  }

  override def toString = f"$name%20s: ${acc}%5dms"
}

/** Implements a stopwatch for profiling purposes */
class Stopwatch(name: String = "Stopwatch") {
  var beginning: Long = 0L
  var end: Long = 0L
  var acc: Long = 0L

  def start: this.type = {
    beginning = System.currentTimeMillis
    end       = 0L
    this
  }

  def stop() {
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
    
  def profile[T](block: => T): T = {
    if (isRunning) stop()
    
    start
    val result = block    // call-by-name
    stop()
    
    result
  }

  def isRunning = beginning != 0L

  override def toString = f"$name%20s: $getMillis%5d${if (isRunning) "..." else ""}ms"
}

object StopwatchCollections {
  private var all = Map[String, StopwatchCollection]()

  def get(name: String): StopwatchCollection = all.getOrElse(name, {
    val sw = new StopwatchCollection(name)
    all += name -> sw
    sw
  })

  def getAll = all
}
