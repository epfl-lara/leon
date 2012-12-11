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
    "  --with-code          Allows the compiler to keep running after the static analysis" + "\n" +
    "  --parse              Checks only whether the program is valid PureScala" + "\n" +
    "  --axioms             Generate simple forall axioms for recursive functions when possible" + "\n" + 
    "  --tolerant           Silently extracts non-pure function bodies as ''unknown''" + "\n" +
    "  --bapa               Use BAPA Z3 extension (incompatible with many other things)" + "\n" +
    "  --impure             Generate testcases only for impure functions" + "\n" +
    "  --testcases=[1,2]    Number of testcases to generate per function" + "\n" +
    "  --testbounds=l:u     Lower and upper bounds for integers in recursive datatypes" + "\n" +
    "  --timeout=N          Sets a timeout of N seconds" + "\n" +
    "  --quickcheck         Use QuickCheck-like random search" + "\n" +
    "  --parallel           Run all solvers in parallel" + "\n" +
    "  --debug=[1-5]        Debug level" + "\n" +
    "  --imperative         Preprocessing and transformation from imperative programs" + "\n" +
    "  --synthesis          Magic!"
  )

  /** Processes the command-line options. */
  private def splitList(lst: String) : Seq[String] = lst.split(':').map(_.trim).filter(!_.isEmpty)
  override def processOptions(options: List[String], error: String => Unit) {
    for(option <- options) {
      option match {
        case "with-code"     =>                     leon.Settings.stopAfterAnalysis = false
        case "uniqid"        =>                     leon.Settings.showIDs = true
        case "parse"         =>                     leon.Settings.stopAfterExtraction = true
        case "tolerant"      =>                     leon.Settings.silentlyTolerateNonPureBodies = true
        case "bapa"          =>                     leon.Settings.useBAPA = true
        case "impure"        =>                     leon.Settings.impureTestcases = true
        case "quickcheck"    =>                     leon.Settings.useQuickCheck = true
        case "parallel"      =>                     leon.Settings.useParallel = true
        case "imperative"     =>                    leon.Settings.synthesis = false;
                                                    leon.Settings.transformProgram = true;
        case "synthesis"     =>                     leon.Settings.synthesis = true;
                                                    leon.Settings.transformProgram = false;
                                                    leon.Settings.stopAfterTransformation = true;

        case s if s.startsWith("debug=") =>       leon.Settings.debugLevel = try { s.substring("debug=".length, s.length).toInt } catch { case _ => 0 }
        case s if s.startsWith("testbounds=") => leon.Settings.testBounds = try { val l = splitList(s.substring("testBounds=".length, s.length)).map(_.toInt); if (l.size != 2) (0, 3) else (l(0), l(1)) } catch { case _ => (0, 3) }
        case s if s.startsWith("timeout=") => leon.Settings.solverTimeout = try { Some(s.substring("timeout=".length, s.length).toInt) } catch { case _ => None }
        case s if s.startsWith("testcases=") =>  leon.Settings.nbTestcases = try { s.substring("testcases=".length, s.length).toInt } catch { case _ => 1 }
        case _ => error("Invalid option: " + option + "\nValid options are:\n" + optionsHelp.get)
      }
    }
  }

  val components = List(new AnalysisComponent(global, this))
  val descriptions = List[String]("leon analyses")
}
