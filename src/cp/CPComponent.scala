package cp

import scala.tools.nsc._
import scala.tools.nsc.plugins._

class CPComponent(val global: Global, val pluginInstance: CPPlugin)
  extends PluginComponent
  with CodeExtraction
  with CallTransformation
{
  import global._
  import Serialization._

  // This is how it works from 2.8 on..
  override val runsRightAfter: Option[String] = None
  override val runsAfter: List[String] = List("refchecks")

  val phaseName = "constraint-programming"

  /** this is initialized when the Funcheck phase starts*/
  var fresh: scala.tools.nsc.util.FreshNameCreator = null 
  
  protected def stopIfErrors: Unit = {
    if(reporter.hasErrors) {
      throw new Exception("There were errors.")
    }
  }

  def newPhase(prev: Phase) = new CPPhase(prev)

  class CPPhase(prev: Phase) extends StdPhase(prev) {
    def apply(unit: CompilationUnit): Unit = {
      //global ref to freshName creator
      fresh = unit.fresh

      if (Settings.verbose)
        println("Starting CP phase")

      val prog: purescala.Definitions.Program = extractCode(unit)

      if (Settings.verbose)
        println("Analyzing specification functions")
      val analysisReporter = 
        if (Settings.verbose) new purescala.DefaultReporter 
        else new purescala.QuietReporter
      val analysis = new purescala.Analysis(prog, analysisReporter)
      analysis.analyse

      if (Settings.verbose)
        println("Finished analysis, starting transformation")

      val serializedProg = serialize(prog)

      transformCalls(unit, prog, serializedProg)
      if (Settings.verbose)
        println("Finished transformation")
    }
  }
}
