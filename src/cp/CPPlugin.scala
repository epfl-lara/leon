package cp

import scala.tools.nsc
import scala.tools.nsc.{Global,Phase}
import scala.tools.nsc.plugins.{Plugin,PluginComponent}

/** This class is the entry point for the plugin. */
class CPPlugin(val global: Global) extends Plugin {
  import global._

  val name = "constraint-programming"
  val description = "Constraint programming in Scala by LARA."

  var silentlyTolerateNonPureBodies = false

  /** The help message displaying the options for that plugin. */
  override val optionsHelp: Option[String] = Some(
    "  -P:constraint-programming:uniqid             When pretty-printing funcheck trees, show identifiers IDs" + "\n" +
    "  -P:constraint-programming:extensions=ex1:... Specifies a list of qualified class names of extensions to be loaded" + "\n" +
    "  -P:constraint-programming:nodefaults         Runs only the analyses provided by the extensions" + "\n" +
    "  -P:constraint-programming:functions=fun1:... Only generates verification conditions for the specified functions" + "\n" +
    "  -P:constraint-programming:unrolling=[0,1,2]  Unrolling depth for recursive functions" + "\n" + 
    "  -P:constraint-programming:axioms             Generate simple forall axioms for recursive functions when possible" + "\n" + 
    "  -P:constraint-programming:tolerant           Silently extracts non-pure function bodies as ''unknown''" + "\n" +
    "  -P:constraint-programming:bapa               Use BAPA Z3 extension" + "\n" +
    "  -P:constraint-programming:XP                 Enable weird transformations and other bug-producing features" + "\n" +
    "  -P:constraint-programming:BV                 Use bit-vectors for integers" + "\n" +
    "  -P:constraint-programming:prune              Use additional SMT queries to rule out some unrollings" + "\n" +
    "  -P:constraint-programming:cores              Use UNSAT cores in the unrolling/refinement step" + "\n" +
    "  -P:constraint-programming:noLuckyTests       Do not perform additional tests to potentially find models early" + "\n" +
    "  -P:constraint-programming:scalaEval          Use functions stored in constraints to evaluate models" + "\n" +
    "  -P:constraint-programming:templates          Use new ``FunctionTemplate'' technique" + "\n" +
    "  -P:constraint-programming:verbose            Print solver output."
  )

  /** Processes the command-line options. */
  private def splitList(lst: String) : Seq[String] = lst.split(':').map(_.trim).filter(!_.isEmpty)
  override def processOptions(options: List[String], error: String => Unit) {
    for(option <- options) {
      option match {
        case "uniqid"     =>                     purescala.Settings.showIDs = true
        case "tolerant"   =>                     silentlyTolerateNonPureBodies = true
        case "nodefaults" =>                     purescala.Settings.runDefaultExtensions = false
        case "axioms"     =>                     purescala.Settings.noForallAxioms = false
        case "bapa"     =>                       purescala.Settings.useBAPA = true
        case "XP"         =>                     purescala.Settings.experimental = true
        case "BV"         =>                     purescala.Settings.bitvectorBitwidth = Some(32)
        case "prune"     =>                      purescala.Settings.pruneBranches = true
        case "cores"     =>                      purescala.Settings.useCores = true
        case "noLuckyTests" =>                   purescala.Settings.luckyTest = false
        case "templates"  =>                     purescala.Settings.useTemplates = true
        case "scalaEval" =>                      cp.Settings.useScalaEvaluator = true
        case "verbose"   =>                      cp.Settings.verbose = true
        case s if s.startsWith("extensions=") => purescala.Settings.extensionNames = splitList(s.substring("extensions=".length, s.length))
        case s if s.startsWith("functions=") =>  purescala.Settings.functionsToAnalyse = Set(splitList(s.substring("functions=".length, s.length)): _*)
        case s if s.startsWith("unrolling=") =>  purescala.Settings.unrollingLevel = try { s.substring("unrolling=".length, s.length).toInt } catch { case _ => 0 }
        case _ => error("Invalid option: " + option)
      }
    }
  }

  val components = List[PluginComponent](new CPComponent(global, this))}
