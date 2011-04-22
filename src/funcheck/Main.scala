package funcheck

import scala.tools.nsc.{Global,Settings,SubComponent,CompilerCommand}

import purescala.Definitions.Program

object Main {
  import purescala.{Reporter,DefaultReporter,Definitions,Analysis}
  import Definitions.Program

  def main(args : Array[String]) : Unit = run(args)

  def runFromString(program : String, args : Array[String], reporter : Reporter = new DefaultReporter, classPath : Option[Seq[String]] = None) : Unit = {
    import java.io.{BufferedWriter,File,FileWriter,IOException}

    try {
      val file : File = File.createTempFile("leon", ".scala")
      file.deleteOnExit
      val out = new BufferedWriter(new FileWriter(file))
      out.write(program)
      out.close
      run(file.getPath.toString +: args, reporter, classPath)
    } catch {
      case e : IOException => reporter.error(e.getMessage)
    }
  }

  def run(args: Array[String], reporter: Reporter = new DefaultReporter, classPath : Option[Seq[String]] = None) : Unit = {
    val settings = new Settings
    classPath.foreach(s => settings.classpath.tryToSet(s.toList))
    runWithSettings(args, settings, s => reporter.info(s), Some(p => defaultAction(p, reporter)))
  }

  private def defaultAction(program: Program, reporter: Reporter) : Unit = {
    val analysis = new Analysis(program, reporter)
    analysis.analyse
  }

  private def runWithSettings(args : Array[String], settings : Settings, printerFunction : String=>Unit, actionOnProgram : Option[Program=>Unit] = None) : Unit = {
    val (funcheckOptions, nonfuncheckOptions) = args.toList.partition(_.startsWith("--"))
    val command = new CompilerCommand(nonfuncheckOptions, settings) {
      override val cmdName = "funcheck"
    }

    if(command.ok) {
      if(settings.version.value) {
        println(command.cmdName + " beta.")
      } else {
        val runner = new PluginRunner(settings, printerFunction, actionOnProgram)
        runner.funcheckPlugin.processOptions(funcheckOptions.map(_.substring(2)), Console.err.println(_))
        //runner.funcheckPlugin.stopAfterExtraction = false
        runner.funcheckPlugin.stopAfterAnalysis = false
        val run = new runner.Run
        run.compile(command.files)
      }
    }
  }
}

/** This class is a compiler that will be used for running the plugin in
 * standalone mode. Original version courtesy of D. Zufferey. */
class PluginRunner(settings : Settings, reportingFunction : String => Unit, actionOnProgram : Option[Program=>Unit]) extends Global(settings, new SimpleReporter(settings, reportingFunction)) {
    val funcheckPlugin = new FunCheckPlugin(this, actionOnProgram)

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
