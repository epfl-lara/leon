package leon
package plugin

import scala.tools.nsc.Settings
import scala.tools.nsc.reporters.AbstractReporter
import scala.tools.nsc.util._
import scala.tools.util.StringOps

/** This implements a reporter that calls the callback with every line that a
regular ConsoleReporter would display. */
class SimpleReporter(val settings: Settings, reporter: leon.Reporter) extends AbstractReporter {
  final val ERROR_LIMIT = 5

  private def label(severity: Severity): String = severity match {
    case ERROR   => "error"
    case WARNING => "warning"
    case INFO    => null
  }

  private def clabel(severity: Severity): String = {
    val label0 = label(severity)
    if (label0 eq null) "" else label0 + ": "
  }

  private def getCountString(severity: Severity): String =
    StringOps.countElementsAsString((severity).count, label(severity))

  /** Prints the message. */
  def printMessage(msg: String) { reporter.info(msg) }

  /** Prints the message with the given position indication. */
  def printMessage(posIn: Position, msg: String) {
    val pos = if (posIn eq null) NoPosition
              else if (posIn.isDefined) posIn.inUltimateSource(posIn.source)
              else posIn
    pos match {
      case FakePos(fmsg) =>
        printMessage(fmsg+" "+msg)
      case NoPosition =>
        printMessage(msg)
      case _ =>
        val buf = new StringBuilder(msg)
        val file = pos.source.file
        printMessage(pos.line + ": " + msg)
        printSourceLine(pos)
    }
  }
  def print(pos: Position, msg: String, severity: Severity) {
    printMessage(pos, clabel(severity) + msg)
  }

  def printSourceLine(pos: Position) {
    printMessage(pos.lineContent.stripLineEnd)
    printColumnMarker(pos)
  }

  def printColumnMarker(pos: Position) = 
    if (pos.isDefined) { printMessage(" " * (pos.column - 1) + "^") }
  
  def printSummary() {
    if (WARNING.count > 0) printMessage(getCountString(WARNING) + " found")
    if (  ERROR.count > 0) printMessage(getCountString(ERROR  ) + " found")
  }

  def display(pos: Position, msg: String, severity: Severity) {
    severity.count += 1
    if (severity != ERROR || severity.count <= ERROR_LIMIT)
      print(pos, msg, severity)
  }

  def displayPrompt: Unit = {}
}
