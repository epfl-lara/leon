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
    if (verbose) println("Stopwatch %-25s: %-3.3fs" format (description, seconds))
    Stopwatch.timeLog += 
      (description -> (Stopwatch.timeLog.getOrElse(description, Nil) :+ seconds))
    seconds
  }
}

object Stopwatch {
  val timeLog = scala.collection.mutable.Map[String, Seq[Double]]()

  def printSummary : Unit = {
    val toPrint = timeLog.map{case (k, v) => ("%-25s" format k, v.foldLeft(0.0){case (a, b) => a + b})}.mkString("\n")

    println("Total times per stopwatch description")
    println(toPrint)
  }
}
