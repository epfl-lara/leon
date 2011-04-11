package funcheck

import scala.tools.nsc._
import scala.tools.nsc.plugins._

class AnalysisComponent(val global: Global, val pluginInstance: FunCheckPlugin)
  extends PluginComponent
  with CodeExtraction
{
  import global._

  // This is how it works from 2.8 on..
  override val runsRightAfter: Option[String] = None
  override val runsAfter: List[String] = List("refchecks")

  val phaseName = pluginInstance.name

  /** this is initialized when the Funcheck phase starts*/
  var fresh: scala.tools.nsc.util.FreshNameCreator = null 
  
  protected def stopIfErrors: Unit = {
    if(reporter.hasErrors) {
      throw new Exception("There were errors.")
    }
  }

  def newPhase(prev: Phase) = new AnalysisPhase(prev)

  class AnalysisPhase(prev: Phase) extends StdPhase(prev) {
    def apply(unit: CompilationUnit): Unit = {
      //global ref to freshName creator
      fresh = unit.fresh

      val prog: purescala.Definitions.Program = extractCode(unit)
      if(pluginInstance.stopAfterExtraction) {
        println("Extracted program for " + unit + ": ")
        println(prog)
        println("Extraction complete. Now terminating the compiler process.")
        exit(0)
      } else {
        if(!pluginInstance.actionAfterExtraction.isDefined) {
          println("Extracted program for " + unit + ". Re-run with -P:funcheck:parse to see the output.")
        }
        //println(prog)
      }

      if(!pluginInstance.actionAfterExtraction.isDefined) {
        println("Starting analysis.")
        val analysis = new purescala.Analysis(prog)
        analysis.analyse
        if(pluginInstance.stopAfterAnalysis) {
          println("Analysis complete. Now terminating the compiler process.")
          exit(0)
        }
      } else {
        pluginInstance.actionAfterExtraction.get(prog)
      }
    }
  }
}
