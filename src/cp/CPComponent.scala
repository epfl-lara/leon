package cp

import scala.tools.nsc._
import scala.tools.nsc.plugins._
import funcheck.CodeExtraction

class CPComponent(val global: Global, val pluginInstance: CPPlugin)
  extends PluginComponent
  with CodeExtraction
  with Serialization
  with CallTransformation
{
  import global._

  // This is how it works from 2.8 on..
  override val runsRightAfter: Option[String] = None
  override val runsAfter: List[String] = List("refchecks")

  val phaseName = "constraint-programming"

  /** this is initialized when the Funcheck phase starts*/
  var fresh: scala.tools.nsc.util.FreshNameCreator = null 
  
  def newPhase(prev: Phase) = new CPPhase(prev)

  class CPPhase(prev: Phase) extends StdPhase(prev) {
    def apply(unit: CompilationUnit): Unit = {
      //global ref to freshName creator
      fresh = unit.fresh

      println("Starting CP phase")

      /*
      def plop(tr: Tree) = tr match {
        case a: Apply =>
          println(a) 
          println(a.fun.getClass) 
        case _ => 
      }
      new ForeachTreeTraverser(plop).traverse(unit.body)
      */

      val prog: purescala.Definitions.Program = extractCode(unit, true)
      val (progString, progId) = serialize(prog)

      transformCalls(unit, prog, progString, progId)
      println("Finished transformation")
    }
  }
}
