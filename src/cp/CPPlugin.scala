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
    "  -P:constraint-programming:nobapa             Disable BAPA Z3 extension" + "\n" +
    "  -P:constraint-programming:XP                 Enable weird transformations and other bug-producing features" + "\n" +
    "  -P:constraint-programming:PLDI               PLDI 2011 settings. Now frozen. Not completely functional. See CAV." + "\n" +
    "  -P:constraint-programming:CAV                CAV 2011 settings. In progress." + "\n" +
    "  -P:constraint-programming:prune              (with CAV) Use additional SMT queries to rule out some unrollings." + "\n" +
    "  -P:constraint-programming:cores              (with CAV) Use UNSAT cores in the unrolling/refinement step."
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
        case "nobapa"     =>                     purescala.Settings.useBAPA = false
        case "newPM"      =>                     { println("''newPM'' is no longer a command-line option, because the new translation is now on by default."); System.exit(0) }
        case "XP"         =>                     purescala.Settings.experimental = true
        case "PLDI"       =>                     { purescala.Settings.experimental = true; purescala.Settings.useInstantiator = true; purescala.Settings.useFairInstantiator = false; purescala.Settings.useBAPA = false; purescala.Settings.zeroInlining = true }
        case "CAV"       =>                      { purescala.Settings.experimental = true; purescala.Settings.useInstantiator = false; purescala.Settings.useFairInstantiator = true; purescala.Settings.useBAPA = false; purescala.Settings.zeroInlining = true }
        case "prune"     =>                      purescala.Settings.pruneBranches = true
        case "cores"     =>                      purescala.Settings.useCores = true
        case s if s.startsWith("unrolling=") =>  purescala.Settings.unrollingLevel = try { s.substring("unrolling=".length, s.length).toInt } catch { case _ => 0 }
        case s if s.startsWith("functions=") =>  purescala.Settings.functionsToAnalyse = Set(splitList(s.substring("functions=".length, s.length)): _*)
        case s if s.startsWith("extensions=") => purescala.Settings.extensionNames = splitList(s.substring("extensions=".length, s.length))
        case _ => error("Invalid option: " + option)
      }
    }
  }

  val components = List[PluginComponent](new CPComponent(global, this))}
