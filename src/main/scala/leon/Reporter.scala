/* Copyright 2009-2014 EPFL, Lausanne */

package leon

import utils._

abstract class Reporter(settings: Settings) {

  abstract class Severity
  case object INFO    extends Severity
  case object WARNING extends Severity
  case object ERROR   extends Severity
  case object FATAL   extends Severity
  case object INTERNAL extends Severity
  case class  DEBUG(section: DebugSection) extends Severity

  case class Message(severity: Severity, position: Position, msg: Any)

  private var _errorCount : Int = 0
  private var _warningCount : Int = 0

  final def errorCount : Int = _errorCount
  final def warningCount : Int = _warningCount

  def account(msg: Message): Message = {
    msg.severity match {
      case WARNING                  => _warningCount += 1
      case ERROR | FATAL | INTERNAL => _errorCount += 1
      case _                        =>
    }

    msg
  }

  def emit(msg: Message): Unit

  def onFatal(): Nothing = {
    throw LeonFatalError(None)
  }

  def onCompilerProgress(current: Int, total: Int) = {}

  final def info(pos: Position, msg: Any): Unit    = emit(account(Message(INFO, pos, msg)))
  final def warning(pos: Position, msg: Any): Unit = emit(account(Message(WARNING, pos, msg)))
  final def error(pos: Position, msg: Any): Unit   = emit(account(Message(ERROR, pos, msg)))

  final def fatalError(pos: Position, msg: Any): Nothing = {
    emit(account(Message(FATAL, pos, msg)))
    onFatal()
  }
  final def internalError(pos: Position, msg : Any) : Nothing = {
    emit(account(Message(INTERNAL, pos, msg.toString + 
      "\nPlease inform the authors of Leon about this message"
    ))) 
    onFatal()
  }
  final def internalAssertion(cond : Boolean, pos: Position, msg : Any) : Unit = {
    if (!cond) internalError(pos,msg)
  }

  def terminateIfError() = {
    if (errorCount > 0) {
      _errorCount = 0
      _warningCount = 0
      fatalError("There were errors.")
    }
  }

  // Debugging
  private val debugMask = settings.debugSections.foldLeft(0){ _ | _.mask }

  def ifDebug(body: (Any => Unit) => Any)(implicit section: DebugSection) = {
    if ((debugMask & section.mask) == section.mask) {
      body( { (msg: Any) => emit(account(Message(DEBUG(section), NoPosition, msg))) } )
    }
  }

  def whenDebug(section: DebugSection)(body: (Any => Unit) => Any) {
    if ((debugMask & section.mask) == section.mask) {
      body( { (msg: Any) => emit(account(Message(DEBUG(section), NoPosition, msg))) } )
    }
  }


  def debug(pos: Position, msg: => Any)(implicit section: DebugSection): Unit = {
    ifDebug{ debug =>
      debug(msg)
    }(section)
  }


  // No-position alternatives
  final def info(msg: Any): Unit          = info(NoPosition, msg)
  final def warning(msg: Any): Unit       = warning(NoPosition, msg)
  final def error(msg: Any): Unit         = error(NoPosition, msg)
  final def fatalError(msg: Any): Nothing = fatalError(NoPosition, msg)
  final def internalError(msg: Any) : Nothing = internalError(NoPosition, msg)
  final def internalAssertion(cond : Boolean, msg: Any) : Unit = internalAssertion(cond,NoPosition, msg)
  final def debug(msg: => Any)(implicit section: DebugSection): Unit = debug(NoPosition, msg)
}

class DefaultReporter(settings: Settings) extends Reporter(settings) {
  protected def severityToPrefix(sev: Severity): String = sev match {
    case ERROR    => "["+Console.RED              +" Error  "+Console.RESET+"]"
    case WARNING  => "["+Console.YELLOW           +"Warning "+Console.RESET+"]"
    case INFO     => "["+Console.BLUE             +"  Info  "+Console.RESET+"]"
    case FATAL    => "["+Console.RED+Console.BOLD +" Fatal  "+Console.RESET+"]"
    case INTERNAL => "["+            Console.BOLD +"Internal"+Console.RESET+"]"
    case DEBUG(_) => "["+Console.MAGENTA          +" Debug  "+Console.RESET+"]"
  }

  def emit(msg: Message) = {
    val posString = if (msg.position != NoPosition) { msg.position+": " } else { "" }

    println(reline(severityToPrefix(msg.severity), posString + msg.msg.toString))
    printLineContent(msg.position)
  }

  protected var linesOf = Map[java.io.File, List[String]]()

  def getLine(pos: Position): Option[String] = {
    val lines = linesOf.get(pos.file) match {
      case Some(lines) =>
        lines
      case None =>
        val lines = if (pos == NoPosition) {
          Nil
        } else {
          scala.io.Source.fromFile(pos.file).getLines.toList
        }

        linesOf += pos.file -> lines
        lines
    }

    if (lines.size > pos.line-1 && pos.line >= 0) {
      Some(lines(pos.line-1))
    } else {
      None
    }
  }

  val prefixSize = 11

  val blankPrefix = " " * prefixSize

  def printLineContent(pos: Position): Unit = {
    getLine(pos) match {
      case Some(line) =>
        println(blankPrefix+line)
        pos match {
          case rp: RangePosition =>
            val bp = rp.focusBegin
            val ep = rp.focusEnd

            val carret = if (bp.line == ep.line) {
              val width = Math.max(ep.col - bp.col, 1)
              "^" * width
            } else {
              val width = Math.max(line.length+1-bp.col, 1)
              ("^" * width)+"..."
            }

            println(blankPrefix+(" " * (bp.col - 1) + Console.RED+carret+Console.RESET))

          case op: OffsetPosition =>
            println(blankPrefix+(" " * (op.col - 1) + Console.RED+"^"+Console.RESET))
        }
      case None =>
    }
  }

  protected def reline(pfx: String, msg: String) : String = {
    pfx+" "+msg.replaceAll("\n", "\n" + (" " * prefixSize))
  }

}

class PlainTextReporter(settings: Settings) extends DefaultReporter(settings) {
  override protected def severityToPrefix(sev: Severity): String = sev match {
    case ERROR    => "[ Error  ]"
    case WARNING  => "[Warning ]"
    case INFO     => "[  Info  ]"
    case FATAL    => "[ Fatal  ]"
    case INTERNAL => "[Internal]"
    case DEBUG(_) => "[ Debug  ]"
  }
}
