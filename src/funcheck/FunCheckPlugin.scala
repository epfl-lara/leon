package funcheck

import scala.tools.nsc
import scala.tools.nsc.{Global,Phase}
import scala.tools.nsc.plugins.{Plugin,PluginComponent}

/** This class is the entry point for the plugin. */
class FunCheckPlugin(val global: Global) extends Plugin {
  import global._

  val name = "funcheck"
  val description = "Static analysis for Scala by LARA."

  var stopAfterAnalysis: Boolean = true

  /** The help message displaying the options for that plugin. */
  override val optionsHelp: Option[String] = Some(
    "  -P:funcheck:uniqid             When pretty-printing funcheck trees, show identifiers IDs" + "\n" +
    "  -P:funcheck:with-code          Allows the compiler to keep running after the static analysis" + "\n" +
    "  -P:funcheck:extensions=ex1:... Specifies a list of qualified class names of extensions to be loaded"
  )

  /** Processes the command-line options. */
  override def processOptions(options: List[String], error: String => Unit) {
    for(option <- options) {
      option match {
        case "with-code" =>                      stopAfterAnalysis = false
        case "uniqid"    =>                      purescala.Settings.showIDs = true
        case s if s.startsWith("extensions=") => purescala.Settings.extensionNames = s.substring("extensions=".length, s.length)
        case _ => error("Invalid option: " + option)
      }
    }
  }

  val components = List[PluginComponent](new AnalysisComponent(global, this))
}
