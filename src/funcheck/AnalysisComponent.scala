package funcheck

import scala.tools.nsc._
import scala.tools.nsc.plugins._

class AnalysisComponent(val global: Global, val pluginInstance: FunCheckPlugin) extends PluginComponent
  with Extractors
  with CodeExtraction
  with ForallInjection
{
  import global._

  // when we use 2.8.x, swap the following two lines
  val runsAfter = "refchecks"
  // override val runsRightAfter = "refchecks"

  val phaseName = pluginInstance.name

  private def stopIfErrors: Unit = {
    if(reporter.hasErrors) {
      println("There were errors.")
      exit(0)
    }
  }

  def newPhase(prev: Phase) = new AnalysisPhase(prev)

  class AnalysisPhase(prev: Phase) extends StdPhase(prev) {
    def apply(unit: CompilationUnit): Unit = {
      (new ForeachTreeTraverser(firstFilter(unit))).traverse(unit.body)
      stopIfErrors
      // (new ForeachTreeTraverser(findContracts)).traverse(unit.body)
      // stopIfErrors

      extractCode(unit)

      if(pluginInstance.stopAfterAnalysis) {
        println("Analysis complete. Now terminating the compiler process.")
        exit(0)
      }
    }

    /** Weeds out programs containing unsupported features. */
    def firstFilter(unit: CompilationUnit)(tree: Tree): Unit = {
      def unsup(s: String): String = "FunCheck: Unsupported construct: " + s

      tree match {
        case ValDef(mods, name, tpt, rhs) if mods.isVariable =>
          unit.error(tree.pos, unsup("mutable variable/field."))
        case LabelDef(name, params, rhs) => unit.error(tree.pos, unsup("loop."))
        case Assign(lhs, rhs) => unit.error(tree.pos, unsup("assignment to mutable variable/field."))
        case Return(expr) => unit.error(tree.pos, unsup("return statement."))
        case Try(block, catches, finalizer) => unit.error(tree.pos, unsup("try block."))
        // case Throw(expr) => unit.error(tree.pos, unsup("throw statement."))
        // case New(tpt) => unit.error(tree.pos, unsup("'new' operator."))
        case SingletonTypeTree(ref) => unit.error(tree.pos, unsup("singleton type."))
        case SelectFromTypeTree(qualifier, selector) => unit.error(tree.pos, unsup("path-dependent type."))
        case CompoundTypeTree(templ: Template) => unit.error(tree.pos, unsup("compound/refinement type."))
        case TypeBoundsTree(lo, hi) => unit.error(tree.pos, unsup("type bounds."))
        case ExistentialTypeTree(tpt, whereClauses) => unit.error(tree.pos, unsup("existential type."))
        case _ => ;
      }
    }
  }
}
