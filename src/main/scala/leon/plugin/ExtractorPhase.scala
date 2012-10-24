package leon
package plugin

import scala.tools.nsc.{Global,Settings=>NSCSettings,SubComponent,CompilerCommand}

object ExtractionPhase extends LeonPhase {

  val name = "Extraction"
  val description = "Extraction of trees from the Scala Compiler"

  def run(ctx: LeonContext): LeonContext = {

    val settings = new NSCSettings
    val compilerOpts = ctx.options.filterNot(_.startsWith("--"))

    val command = new CompilerCommand(compilerOpts, settings) {
      override val cmdName = "leon"
    }

    val newCtx = if(command.ok) {
      val runner = new PluginRunner(settings, ctx)
      val run = new runner.Run
      run.compile(command.files)

      runner.ctx
    } else {
      ctx
    }

    if (newCtx.program.isDefined) {
      newCtx
    } else {
      newCtx.reporter.fatalError("No input program.")
    }
  }
}

/** This class is a compiler that will be used for running the plugin in
 * standalone mode. Original version courtesy of D. Zufferey. */
class PluginRunner(settings : NSCSettings, var ctx: LeonContext) extends Global(settings, new SimpleReporter(settings, ctx.reporter)) {
  val leonPlugin = new LeonPlugin(this)

  protected def myAddToPhasesSet(sub : SubComponent, descr : String) : Unit = {
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
      val zipped = leonPlugin.components zip leonPlugin.descriptions
      zipped
    }
    phs foreach (myAddToPhasesSet _).tupled
  }
}
