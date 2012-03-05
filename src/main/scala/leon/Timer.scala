package leon

/** Creates a thread that, when started, counts for maxsecs seconds and then
 * calls the callback, unless the timer was halted first. */
class Timer(callback : () => Unit, maxSecs : Int) extends Thread {
  private var keepRunning = true
  private val asMillis : Long = 1000L * maxSecs

  override def run : Unit = {
    val startTime : Long = System.currentTimeMillis
    var exceeded : Boolean = false

    while(!exceeded && keepRunning) {
      if(asMillis < (System.currentTimeMillis - startTime)) {
        exceeded = true
      }
      Thread.sleep(100) //is needed on my (regis) machine, if not here, the loop does not stop when halt is called.
    }
    if(exceeded && keepRunning) {
      callback()
    }
  }

  def halt : Unit = {
    keepRunning = false
  }
}
