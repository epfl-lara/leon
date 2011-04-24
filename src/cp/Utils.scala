package cp

object Utils {
  class Timer(description : String, verbose : Boolean = false) {
    var beginning: Long = 0L
    var end: Long = 0L
    def start = {
      beginning = System.currentTimeMillis
    }
    def stop : Double = {
      end = System.currentTimeMillis
      val seconds = (end - beginning) / 1000.0
      if (verbose) println("Timer \"" + description + "\": " + seconds + " s")
      seconds
    }
  }
}
