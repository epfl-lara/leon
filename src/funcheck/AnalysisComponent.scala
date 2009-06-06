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
      (new ForeachTreeTraverser(firstFilter(unit))).traverse(unit.body)
      stopIfErrors
      (new ForeachTreeTraverser(findContracts)).traverse(unit.body)

      if(pluginInstance.stopAfterAnalysis) {
        println("Analysis complete. Now terminating the compiler process.")
        exit(0)
      }
    }

    private def stopIfErrors: Nothing = {
      if(reporter.hasErrors) println("There were errors.")
      exit(0)
    }

    private def findContracts(tree: Tree): Unit = tree match {
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

    /** Weeds out programs containing unsupported features. */
    def firstFilter(unit: CompilationUnit)(tree: Tree): Unit = {
      def unsup(s: String): String = "FunCheck: Unsupported construct: " + s

      tree match {
        case c @ ClassDef(mods, name, tparams, impl) => {
          val s = c.symbol
          
          println(s)

          if(s.isTrait)
            unit.error(tree.pos, unsup("trait."))

          else if(s.isModule) 
            println("Seems like " + name + " is an object.")

          else if(s.isClass && !(mods.isCase || mods.isAbstract)) 
            unit.error(tree.pos, unsup("non-abstract, non-case class."))
          
        }
        case ValDef(mods, name, tpt, rhs) if mods.isVariable =>
          unit.error(tree.pos, unsup("mutable variable/field."))
        case LabelDef(name, params, rhs) => unit.error(tree.pos, unsup("loop."))
        case Assign(lhs, rhs) => unit.error(tree.pos, unsup("assignment to mutable variable/field."))
        case Return(expr) => unit.error(tree.pos, unsup("return statement."))
        case Try(block, catches, finalizer) => unit.error(tree.pos, unsup("try block."))
        case Throw(expr) => unit.error(tree.pos, unsup("throw statement."))
        case New(tpt) => unit.error(tree.pos, unsup("'new' operator."))
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
