package funcheck

import scala.tools.nsc._
import scala.tools.nsc.plugins._
import scalacheck._	

class AnalysisComponent(val global: Global, val pluginInstance: FunCheckPlugin)
  extends PluginComponent
  with NameAnalyzer
  with CodeExtraction
  // with ScalaCheckIntegrator // Mirco's stuff.
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
      println("There were errors.")
      exit(0)
    }
  }

  def newPhase(prev: Phase) = new AnalysisPhase(prev)

  class AnalysisPhase(prev: Phase) extends StdPhase(prev) {
    def apply(unit: CompilationUnit): Unit = {
      //global ref to freshName creator
      fresh = unit.fresh
      
      // That filter just helps getting meaningful errors before the attempt to
      // extract the code, but it's really optional.
      // (new ForeachTreeTraverser(firstFilter(unit))).traverse(unit.body)
      // stopIfErrors

      val prog: purescala.Definitions.Program = extractCode(unit)
      println("Extracted program for " + unit + ": ")
      println(prog)

      // Mirco your component can do its job here, as I leave the trees
      // unmodified.
      // val (genDef, arbDef) = createGeneratorDefDefs(unit)
    
      // injectGenDefDefs(genDef ::: arbDef, unit)
      // forAllTransform(unit)

      if(pluginInstance.stopAfterAnalysis) {
        println("Analysis complete. Now terminating the compiler process.")
        exit(0)
      }
    }

    /** Weeds out some programs containing unsupported features. */
    // def firstFilter(unit: CompilationUnit)(tree: Tree): Unit = {
    //   def unsup(s: String): String = "FunCheck: Unsupported construct: " + s

    //   tree match {
    //     case ValDef(mods, name, tpt, rhs) if mods.isVariable =>
    //       unit.error(tree.pos, unsup("mutable variable/field."))
    //     case LabelDef(name, params, rhs) => unit.error(tree.pos, unsup("loop."))
    //     case Assign(lhs, rhs) => unit.error(tree.pos, unsup("assignment to mutable variable/field."))
    //     case Return(expr) => unit.error(tree.pos, unsup("return statement."))
    //     case Try(block, catches, finalizer) => unit.error(tree.pos, unsup("try block."))
    //     case SingletonTypeTree(ref) => unit.error(tree.pos, unsup("singleton type."))
    //     case SelectFromTypeTree(qualifier, selector) => unit.error(tree.pos, unsup("path-dependent type."))
    //     case CompoundTypeTree(templ: Template) => unit.error(tree.pos, unsup("compound/refinement type."))
    //     case TypeBoundsTree(lo, hi) => unit.error(tree.pos, unsup("type bounds."))
    //     case ExistentialTypeTree(tpt, whereClauses) => unit.error(tree.pos, unsup("existential type."))
    //     case _ => ;
    //   }
    // }
  }
  
  
  
}
