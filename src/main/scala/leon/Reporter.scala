/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import purescala.Definitions.Definition
import purescala.Trees.Expr
import purescala.PrettyPrinter

abstract class Reporter {
  def infoFunction(msg: Any) : Unit 
  def warningFunction(msg: Any) : Unit 
  def errorFunction(msg: Any) : Unit
  def fatalErrorFunction(msg: Any) : Nothing

  // This part of the implementation is non-negociable.
  private var _errorCount : Int = 0
  private var _warningCount : Int = 0

  final def errorCount : Int = _errorCount
  final def warningCount : Int = _warningCount

  final def info(msg: Any) = infoFunction(msg)
  final def warning(msg: Any) = {
    _warningCount += 1
    warningFunction(msg)
  }
  final def error(msg: Any) = {
    _errorCount += 1
    errorFunction(msg)
  }
  final def fatalError(msg: Any) = {
    _errorCount += 1
    fatalErrorFunction(msg)
  }
}

class DefaultReporter extends Reporter {
  protected val errorPfx   = "[ Error ] "
  protected val warningPfx = "[Warning] "
  protected val infoPfx    = "[ Info  ] "
  protected val fatalPfx   = "[ Fatal ] "

  def output(msg: String) : Unit = println(msg)

  protected def reline(pfx: String, msg: String) : String = {
    val color = if(pfx == errorPfx || pfx == warningPfx || pfx == fatalPfx) {
      Console.RED
    } else {
      Console.BLUE
    }
    "[" + color + pfx.substring(1, pfx.length-2) + Console.RESET + "] " +
    msg.replaceAll("\n", "\n" + (" " * (pfx.size)))
  }

  def errorFunction(msg: Any) = output(reline(errorPfx, msg.toString))
  def warningFunction(msg: Any) = output(reline(warningPfx, msg.toString))
  def infoFunction(msg: Any) = output(reline(infoPfx, msg.toString))
  def fatalErrorFunction(msg: Any) = { output(reline(fatalPfx, msg.toString)); throw LeonFatalError() }
}

class QuietReporter extends DefaultReporter {
  override def warningFunction(msg : Any) = {}
  override def infoFunction(msg : Any) = {}
}

class SilentReporter extends QuietReporter {
  override def errorFunction(msg : Any) = {}
  override def fatalErrorFunction(msg: Any) = throw LeonFatalError()
}
