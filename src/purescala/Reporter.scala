package purescala

import purescala.Definitions.Definition
import purescala.Trees.Expr

abstract class Reporter {
  def error(msg: Any) : Unit
  def warning(msg: Any) : Unit 
  def info(msg: Any) : Unit 
  def fatalError(msg: Any) : Nothing

  def error(definition: Definition, msg: Any) : Unit = error(msg)
  def warning(definition: Definition, msg: Any) : Unit = warning(msg)
  def info(definition: Definition, msg: Any) : Unit = info(msg)
  def fatalError(definition: Definition, msg: Any) : Nothing = fatalError(msg)

  def error(expr: Expr, msg: Any) : Unit = error(msg)
  def warning(expr: Expr, msg: Any) : Unit = warning(msg)
  def info(expr: Expr, msg: Any) : Unit = info(msg)
  def fatalError(expr: Expr, msg: Any) : Nothing = fatalError(msg)
}

class DefaultReporter extends Reporter {
  protected val errorPfx   = "[ Error ] "
  protected val warningPfx = "[Warning] "
  protected val infoPfx    = "[ Info  ] "
  protected val fatalPfx   = "[ Fatal ] "

  def output(msg: String) : Unit = {
    /*Console.err.*/println(msg)
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
  def fatalError(msg: Any) = { output(reline(fatalPfx, msg.toString)); sys.exit(0) }
  override def error(definition: Definition, msg: Any) = output(reline(errorPfx, PrettyPrinter(definition) + "\n" + msg.toString))
  override def warning(definition: Definition, msg: Any) = output(reline(warningPfx, PrettyPrinter(definition) + "\n" + msg.toString))
  override def info(definition: Definition, msg: Any) = output(reline(infoPfx, PrettyPrinter(definition) + "\n" + msg.toString))
  override def fatalError(definition: Definition, msg: Any) = { output(reline(fatalPfx, PrettyPrinter(definition) + "\n" + msg.toString)); sys.exit(0) }
  override def error(expr: Expr, msg: Any) = output(reline(errorPfx, PrettyPrinter(expr) + "\n" + msg.toString)) 
  override def warning(expr: Expr, msg: Any) = output(reline(warningPfx, PrettyPrinter(expr) + "\n" + msg.toString))
  override def info(expr: Expr, msg: Any) = output(reline(infoPfx, PrettyPrinter(expr) + "\n" + msg.toString))
  override def fatalError(expr: Expr, msg: Any) = { output(reline(fatalPfx, PrettyPrinter(expr) + "\n" + msg.toString)); sys.exit(0) }
}

class QuietReporter extends DefaultReporter {
  override def warning(msg: Any) = {}
  override def info(msg: Any) = {}
}
