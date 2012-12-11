package leon
package plugin

import scala.tools.nsc
import scala.tools.nsc.{Global,Phase}
import scala.tools.nsc.plugins.{Plugin,PluginComponent}
import purescala.Definitions.Program

/** This class is the entry point for the plugin. */
class LeonPlugin(val global: PluginRunner) extends Plugin {
  import global._

  val name = "leon"
  val description = "The Leon static analyzer"

  /** The help message displaying the options for that plugin. */
  override val optionsHelp: Option[String] = Some(
    "  --uniqid             When pretty-printing purescala trees, show identifiers IDs" + "\n" +
    "  --tolerant           Silently extracts non-pure function bodies as ''unknown''" + "\n"
  )

  /** Processes the command-line options. */
  private def splitList(lst: String) : Seq[String] = lst.split(':').map(_.trim).filter(!_.isEmpty)
  override def processOptions(options: List[String], error: String => Unit) {
    for(option <- options) {
      option match {
        case "uniqid"        =>                     leon.Settings.showIDs = true
        case "tolerant"      =>                     leon.Settings.silentlyTolerateNonPureBodies = true

        case _ => error("Invalid option: " + option + "\nValid options are:\n" + optionsHelp.get)
      }
    }
  }

  val components = List(new AnalysisComponent(global, this))
  val descriptions = List[String]("leon analyses")
}
