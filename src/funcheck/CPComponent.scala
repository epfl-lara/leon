package funcheck

import scala.tools.nsc._
import scala.tools.nsc.plugins._

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

      val prog: purescala.Definitions.Program = extractCode(unit)
      val filename = writeProgram(prog)
      println("Program extracted and written into: " + filename)

      transformCalls(unit, prog, filename)
      println("Finished transformation")

      /*
      try {
        val recovered = readProgram(filename)
        println
        println("Recovered: " + recovered)
      } catch {
        case e => e.printStackTrace()
      }
      */
    }
  }
}
