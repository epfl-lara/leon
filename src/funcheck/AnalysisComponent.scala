package funcheck

import scala.tools.nsc._
import scala.tools.nsc.plugins._

class AnalysisComponent(val global: Global, val pluginInstance: FunCheckPlugin) extends PluginComponent with Extractors {
  import global._
  import global.definitions._

  // when we use 2.8.x, swap the following two lines
  val runsAfter = "refchecks"
  // override val runsRightAfter = "refchecks"

  val phaseName = pluginInstance.name

  def newPhase(prev: Phase) = new AnalysisPhase(prev)

  class AnalysisPhase(prev: Phase) extends StdPhase(prev) {
    import StructuralExtractors._

    def apply(unit: CompilationUnit): Unit = {
      (new ForeachTreeTraverser(findContracts)).traverse(unit.body)

      if(pluginInstance.stopAfterAnalysis) {
        println("Analysis complete. Now terminating the compiler process.")
        exit(0)
      }
    }

    def findContracts(tree: Tree): Unit = tree match {
      case DefDef(/*mods*/ _, name, /*tparams*/ _, /*vparamss*/ _, /*tpt*/ _, body) => {
        var realBody = body
        var reqCont: Option[Tree] = None
        var ensCont: Option[Function] = None

        body match {
          case EnsuredExpression(body2, contract) => realBody = body2; ensCont = Some(contract)
          case _ => ;
        }

        realBody match {
          case RequiredExpression(body3, contract) => realBody = body3; reqCont = Some(contract)
          case _ => ;
        }

        println("In: " + name) 
        println("  Requires clause: " + reqCont)
        println("  Ensures  clause: " + ensCont)
        println("  Body:            " + realBody)
      }

      case _ => ;
    }
  }
}
