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

object DefaultReporter extends Reporter {
  private val errorPfx = "Error: "
  private val warningPfx = "Warning: "
  private val infoPfx = "Info: "
  private val fatalPfx = "Fatal error: "

  def output(msg: String) : Unit = {
    Console.err.println(msg)
    Console.err.println("")
  }

  def error(msg: Any) = output(errorPfx + msg.toString)
  def warning(msg: Any) = output(warningPfx + msg.toString)
  def info(msg: Any) = output(infoPfx + msg.toString)
  def fatalError(msg: Any) = { output(fatalPfx + msg.toString); exit(0) }
  def error(definition: Definition, msg: Any) = output(errorPfx + "\n" + PrettyPrinter(definition) + msg.toString)
  def warning(definition: Definition, msg: Any) = output(warningPfx + "\n" + PrettyPrinter(definition) + msg.toString)
  def info(definition: Definition, msg: Any) = output(infoPfx + "\n" + PrettyPrinter(definition) + msg.toString)
  def fatalError(definition: Definition, msg: Any) = { output(fatalPfx + "\n" + PrettyPrinter(definition) + msg.toString); exit(0) }
  def error(expr: Expr, msg: Any) = output(errorPfx + "\n" + PrettyPrinter(expr) + msg.toString) 
  def warning(expr: Expr, msg: Any) = output(warningPfx + "\n" + PrettyPrinter(expr) + msg.toString) 
  def info(expr: Expr, msg: Any) = output(infoPfx + "\n" + PrettyPrinter(expr) + msg.toString) 
  def fatalError(expr: Expr, msg: Any) = { output(fatalPfx + "\n" + PrettyPrinter(expr) + msg.toString); exit(0) }
}
