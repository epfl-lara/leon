/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package plugin

import scala.tools.nsc.Settings
import scala.tools.nsc.reporters.AbstractReporter

import scala.reflect.internal.util.{Position, NoPosition, FakePos, StringOps}

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
  def printMessage(msg: String, severity: Severity) {
    severity match {
      case ERROR =>
        reporter.error(msg)
      case WARNING =>
        reporter.warning(msg)
      case INFO =>
        reporter.info(msg)
    }
  }

  /** Prints the message with the given position indication. */
  def printMessage(posIn: Position, msg: String, severity: Severity) {
    val pos = if (posIn eq null) NoPosition
              else if (posIn.isDefined) posIn.inUltimateSource(posIn.source)
              else posIn
    pos match {
      case FakePos(fmsg) =>
        printMessage(fmsg+" "+msg, severity)
      case NoPosition =>
        printMessage(msg, severity)
      case _ =>
        val buf = new StringBuilder(msg)
        val file = pos.source.file
        printMessage(pos.line + ": " + msg+"\n"+getSourceLine(pos), severity)
    }
  }
  def print(pos: Position, msg: String, severity: Severity) {
    printMessage(pos, clabel(severity) + msg, severity)
  }

  def getSourceLine(pos: Position) = {
    pos.lineContent.stripLineEnd+getColumnMarker(pos)
  }

  def getColumnMarker(pos: Position) = if (pos.isDefined) { 
      "\n"+(" " * (pos.column - 1) + "^")
    } else {
      ""
    }
  
  def printSummary() {
    if (WARNING.count > 0) printMessage(getCountString(WARNING) + " found", INFO)
    if (  ERROR.count > 0) printMessage(getCountString(ERROR  ) + " found", INFO)
  }

  def display(pos: Position, msg: String, severity: Severity) {
    severity.count += 1
    if (severity != ERROR || severity.count <= ERROR_LIMIT)
      print(pos, msg, severity)
  }

  def displayPrompt: Unit = {}
}
