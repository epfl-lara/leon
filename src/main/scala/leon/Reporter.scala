/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import purescala.Definitions.Definition
import purescala.Trees.Expr
import purescala.PrettyPrinter
import scala.annotation.implicitNotFound

abstract class Reporter(settings: Settings) {
  def infoFunction(msg: Any) : Unit
  def warningFunction(msg: Any) : Unit
  def errorFunction(msg: Any) : Unit
  def debugFunction(msg: Any) : Unit
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

  private val debugMask = settings.debugSections.foldLeft(0){ _ | _.mask }

  def ifDebug(body: (Any => Unit) => Any)(implicit section: DebugSection) = {
    if ((debugMask & section.mask) == section.mask) {
      body(debugFunction)
    }
  }

  def whenDebug(section: DebugSection)(body: (Any => Unit) => Any) {
    if ((debugMask & section.mask) == section.mask) {
      body(debugFunction)
    }
  }

  def debug(msg: => Any)(implicit section: DebugSection) = {
    ifDebug{ debug =>
      debug(msg)
    }(section)
  }
}

class DefaultReporter(settings: Settings) extends Reporter(settings) {
  protected val errorPfx   = "[ Error ] "
  protected val warningPfx = "[Warning] "
  protected val infoPfx    = "[ Info  ] "
  protected val fatalPfx   = "[ Fatal ] "
  protected val debugPfx   = "[ Debug ] "

  def output(msg: String) : Unit = println(msg)

  protected def reline(pfx: String, msg: String) : String = {
    val color = if(pfx == errorPfx || pfx == fatalPfx) {
      Console.RED
    } else if(pfx == warningPfx) {
      Console.YELLOW
    } else if(pfx == debugPfx) {
      Console.MAGENTA
    } else {
      Console.BLUE
    }
    "[" + color + pfx.substring(1, pfx.length-2) + Console.RESET + "] " +
    msg.replaceAll("\n", "\n" + (" " * (pfx.size)))
  }

  def errorFunction(msg: Any)   = output(reline(errorPfx, msg.toString))
  def warningFunction(msg: Any) = output(reline(warningPfx, msg.toString))
  def infoFunction(msg: Any)    = output(reline(infoPfx, msg.toString))
  def debugFunction(msg: Any)   = output(reline(debugPfx, msg.toString))
  def fatalErrorFunction(msg: Any) = {
    output(reline(fatalPfx, msg.toString));
    throw LeonFatalError()
  }
}

@implicitNotFound("No implicit debug section found in scope. You need define an implicit DebugSection to use debug/ifDebug")
sealed abstract class DebugSection(val name: String, val mask: Int)

case object DebugSectionSolver       extends DebugSection("solver",       1 << 0)
case object DebugSectionSynthesis    extends DebugSection("synthesis",    1 << 1)
case object DebugSectionTimers       extends DebugSection("timers",       1 << 2)
case object DebugSectionOptions      extends DebugSection("options",      1 << 3)
case object DebugSectionVerification extends DebugSection("verification", 1 << 4)

object DebugSections {
  val all = Set[DebugSection](
    DebugSectionSolver,
    DebugSectionSynthesis,
    DebugSectionTimers,
    DebugSectionOptions,
    DebugSectionVerification
  )
}
