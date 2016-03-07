/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package utils

import scala.language.dynamics

/** Implements a timer for profiling purposes */
class Timer() {
  var beginning: Long = 0L
  var end: Long = 0L
  var runs: List[Long] = Nil

  def start: this.type = {
    beginning = System.currentTimeMillis
    end       = 0L
    this
  }

  def restart: this.type = {
    beginning = 0L
    end = 0L
    runs = Nil

    start
  }

  def stop = {
    end         = System.currentTimeMillis
    runs      ::= (end - beginning)
    beginning   = 0L
    runs.head
  }

  def isRunning = beginning != 0L

  override def toString = {
    val n = runs.size

    if (n == 0) {
      "N/A"
    } else if (n > 1) {
      val tot = runs.sum
      val min = runs.min
      val max = runs.max

      f"(min: $min%3d, avg: ${tot / n}%3d, max: $max%3d, n: $n%3d) $tot%6d ms"
    } else {
      val tot = runs.sum

      f"$tot%6d ms"
    }
  }
}

class TimerStorage extends Dynamic {
  var keys    = List[String]()
  var fields  = Map[String, TimerStorage]()
  var selfTimer: Option[Timer] = None

  def get(name: String): TimerStorage = {
    fields.get(name) match {
      case Some(t) =>
        t

      case None =>
        val t = new TimerStorage()
        fields += name -> t
        keys ::= name
        t
    }
  }

  private def isLastKeys(n: String) = Some(n) == keys.headOption

  def selectDynamic(name: String): TimerStorage = get(name)


  def start() = {
    if (selfTimer.isEmpty) {
      selfTimer = Some(new Timer)
    }
    selfTimer.get.start

    this
  }

  def timed[T](b: => T): T = {
    start()
    val res = b
    stop()
    res
  }

  def stop() = {
    selfTimer.get.stop
  }

  def outputTable(printer: String => Unit) = {
    import utils.ASCIIHelpers._

    var table = Table("Timers")

    table += Row(Seq(
        Cell("name"),
        Cell("min",   align = Right),
        Cell("avg",   align = Right),
        Cell("max",   align = Right),
        Cell("n",     align = Right),
        Cell("total", align = Right)
      ))
    table += Separator

    var closed = Set[TimerStorage]()

    def output(ts: TimerStorage, path: List[(TimerStorage, String)]): Unit = {
      val indent = path.map { case (from, name) =>
        if (closed(from)) {
          "  "
        } else if (from.isLastKeys(name)) {
          closed += from
          "└ "
        } else if((from, name) == path.head) {
          "├ "
        } else {
          "│ "
        }
      }.reverse.mkString

      (path, ts.selfTimer) match {
        case ((_, name) :: _, Some(t)) =>
          val n   = t.runs.size
          val tot = t.runs.sum

          val (min: String, avg: String, max: String, n2: String, total: String) = if (n == 0) {
            ("", "", "", "", "N/A")
          } else if (n > 1) {
            val min = t.runs.min
            val max = t.runs.max
            val avg = tot/n
            (f"$min%d ms", f"$avg%d ms", f"$max%d ms", f"$n%d", f"$tot%d ms")
          } else {
            ("", "", "", "", f"$tot%d ms")
          }

          table += Row(Seq(
            Cell(indent+name),
            Cell(min, align = Right),
            Cell(avg, align = Right),
            Cell(max, align = Right),
            Cell(n2,  align = Right),
            Cell(total, align = Right)
          ))
        case ((_, name) :: _, None) =>
          table += Row(Seq(
            Cell(indent+name, 6)
          ))
        case _ =>

      }

      ts.keys.reverseMap(n => n -> ts.fields(n)).foreach { case (name, nts) =>
        output(nts, (ts -> name) :: path)
      }
    }

    if (fields.nonEmpty) {
      output(this, Nil)
    }

    printer(table.render)
  }
}
