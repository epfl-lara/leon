package purescala

import purescala.Definitions.Definition
import purescala.Trees.Expr

abstract class Reporter {
  def error(msg: Any) : Unit
  def warning(msg: Any) : Unit 
  def info(msg: Any) : Unit 
  def fatalError(msg: Any) : Nothing

  def error(definition: Definition, msg: Any) : Unit
  def warning(definition: Definition, msg: Any) : Unit
  def info(definition: Definition, msg: Any) : Unit 
  def fatalError(definition: Definition, msg: Any) : Nothing

  def error(expr: Expr, msg: Any) : Unit
  def warning(expr: Expr, msg: Any) : Unit
  def info(expr: Expr, msg: Any) : Unit
  def fatalError(expr: Expr, msg: Any) : Nothing
}

class DefaultReporter extends Reporter {
  protected val errorPfx   = "[ Error ] "
  protected val warningPfx = "[Warning] "
  protected val infoPfx    = "[ Info  ] "
  protected val fatalPfx   = "[ Fatal ] "

  def output(msg: String) : Unit = {
    Console.err.println(msg)
  }

  protected def reline(pfx: String, msg: String) : String = {
    val color = if(pfx == errorPfx || pfx == warningPfx || pfx == fatalPfx) {
      Console.RED
    } else {
      Console.BLUE
    }
    "[" + color + pfx.substring(1, pfx.length-2) + Console.RESET + "] " +
    msg.trim.replaceAll("\n", "\n" + (" " * (pfx.size)))
  }

  def error(msg: Any) = output(reline(errorPfx, msg.toString))
  def warning(msg: Any) = output(reline(warningPfx, msg.toString))
  def info(msg: Any) = output(reline(infoPfx, msg.toString))
  def fatalError(msg: Any) = { output(reline(fatalPfx, msg.toString)); exit(0) }
  def error(definition: Definition, msg: Any) = output(reline(errorPfx, PrettyPrinter(definition) + "\n" + msg.toString))
  def warning(definition: Definition, msg: Any) = output(reline(warningPfx, PrettyPrinter(definition) + "\n" + msg.toString))
  def info(definition: Definition, msg: Any) = output(reline(infoPfx, PrettyPrinter(definition) + "\n" + msg.toString))
  def fatalError(definition: Definition, msg: Any) = { output(reline(fatalPfx, PrettyPrinter(definition) + "\n" + msg.toString)); exit(0) }
  def error(expr: Expr, msg: Any) = output(reline(errorPfx, PrettyPrinter(expr) + "\n" + msg.toString)) 
  def warning(expr: Expr, msg: Any) = output(reline(warningPfx, PrettyPrinter(expr) + "\n" + msg.toString))
  def info(expr: Expr, msg: Any) = output(reline(infoPfx, PrettyPrinter(expr) + "\n" + msg.toString))
  def fatalError(expr: Expr, msg: Any) = { output(reline(fatalPfx, PrettyPrinter(expr) + "\n" + msg.toString)); exit(0) }
}

class QuietReporter extends DefaultReporter {
  override def warning(msg: Any) = {}
  override def info(msg: Any) = {}
  override def warning(definition: Definition, msg: Any) = {}
  override def info(definition: Definition, msg: Any) = {}
  override def warning(expr: Expr, msg: Any) = {}
  override def info(expr: Expr, msg: Any) = {}
}
