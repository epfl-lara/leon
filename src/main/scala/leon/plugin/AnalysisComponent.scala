package leon
package plugin

import scala.tools.nsc._
import scala.tools.nsc.plugins._

import purescala.Definitions.Program
import synthesis.SynthesisPhase

class AnalysisComponent(val global: Global, val leonReporter: Reporter, val pluginInstance: LeonPlugin)
  extends PluginComponent
  with CodeExtraction
{
  import global._

  // This is how it works from 2.8 on..
  override val runsRightAfter: Option[String] = None
  override val runsAfter: List[String] = List("refchecks")

  val phaseName = pluginInstance.name

  /** this is initialized when the Leon phase starts*/
  var fresh: scala.tools.nsc.util.FreshNameCreator = null 
  
  protected def stopIfErrors: Unit = {
    if(reporter.hasErrors) {
      if(Settings.simpleOutput)
        println("error")
      sys.exit(1)
      //throw new Exception("There were errors.")
    }
  }

  def newPhase(prev: Phase) = new AnalysisPhase(prev)

  class AnalysisPhase(prev: Phase) extends StdPhase(prev) {
    def computeLeonPhases: List[LeonPhase] = {
      List(
        if (Settings.transformProgram) {
          List(
            ArrayTransformation,
            EpsilonElimination,
            ImperativeCodeElimination,
            /*UnitElimination,*/
            FunctionClosure,
            /*FunctionHoisting,*/
            Simplificator
          )
        } else {
          Nil
        }
      ,
        if (Settings.synthesis)
          List(
            new SynthesisPhase(leonReporter)
          )
        else
          Nil
      ,
        if (!Settings.stopAfterTransformation) {
          List(
            AnalysisPhase
          )
        } else {
          Nil
        }
      ).flatten
    }

    def apply(unit: CompilationUnit): Unit = {
      //global ref to freshName creator
      fresh = unit.fresh

      var ac = LeonContext(program = extractCode(unit))

      if(Settings.stopAfterExtraction) {
        leonReporter.info("Extracted program for " + unit + ": ")
        leonReporter.info(ac.program)
        sys.exit(0)
      }

      val phases = computeLeonPhases

      for ((phase, i) <- phases.zipWithIndex) {
        leonReporter.info("%2d".format(i)+": "+phase.name)
        ac = phase.run(ac)
      }

    }
  }
}
