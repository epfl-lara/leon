package funcheck

import scala.tools.nsc.{Global,Settings,SubComponent,CompilerCommand}
import scala.tools.nsc.reporters.{ConsoleReporter,Reporter}

/** This class is a compiler that will be used for running
*  the plugin in standalone mode. Courtesy of D. Zufferey. */
class PluginRunner(settings : Settings, reporter : Reporter) extends Global(settings, reporter) {
  def this(settings : Settings) = this(settings, new ConsoleReporter(settings))

    val funcheckPlugin = new FunCheckPlugin(this)

    protected def addToPhasesSet(sub : SubComponent, descr : String) : Unit = {
    phasesSet += sub
  }

  /** The phases to be run. */
  override protected def computeInternalPhases() : Unit = {
    val phs = List(
      syntaxAnalyzer          -> "parse source into ASTs, perform simple desugaring",
      analyzer.namerFactory   -> "resolve names, attach symbols to named trees",
      analyzer.packageObjects -> "load package objects",
      analyzer.typerFactory   -> "the meat and potatoes: type the trees",
      superAccessors          -> "add super accessors in traits and nested classes",
      pickler                 -> "serialize symbol tables",
      refchecks               -> "reference and override checking, translate nested objects"
    ) ::: {
      val zipped = funcheckPlugin.components zip funcheckPlugin.descriptions
      zipped
    }
    phs foreach (addToPhasesSet _).tupled
  }
}

object Main {
  def main(args: Array[String]): Unit = {
    val settings = new Settings
    runWithSettings(args, settings)
  }

  private def runWithSettings(args : Array[String], settings : Settings) : Unit = {
    val (funcheckOptions, nonfuncheckOptions) = args.toList.partition(_.startsWith("--"))
    val command = new CompilerCommand(nonfuncheckOptions, settings) {
      override val cmdName = "funcheck"
    }

    if(command.ok) {
      if(settings.version.value) {
        println(command.cmdName + " beta.")
      } else {
        val runner = new PluginRunner(settings)
        runner.funcheckPlugin.processOptions(funcheckOptions.map(_.substring(2)), Console.err.println(_))
        val run = new runner.Run
        run.compile(command.files)
      }
    }
  }
}
