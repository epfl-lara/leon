package purescala

/** Implements a stopwatch for profiling purposes */
class Stopwatch(description : String, verbose : Boolean = false) {
  var beginning: Long = 0L
  var end: Long = 0L
  def start : Stopwatch = {
    beginning = System.currentTimeMillis
    this
  }
  def stop : Double = {
    end = System.currentTimeMillis
    val seconds = (end - beginning) / 1000.0
    if (verbose) println("Stopwatch \"" + description + "\": " + seconds + " s")
    seconds
  }
}
