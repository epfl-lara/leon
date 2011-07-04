package plugintest

import scala.tools.nsc
import scala.tools.nsc.{Global,Phase}
import scala.tools.nsc.plugins._

class TestPlugin(val global : Global) extends Plugin {
  import global._

  val name = "test!"
  val description = "Mini plugin to toy with ``MyAny'' type of things"
  
  override val optionsHelp : Option[String] = None

  val components = List[PluginComponent](new Component(global))
  val descriptions : List[String] = List("tests with ``MyAny''")
}

class Component(val global : Global) extends PluginComponent {
  import global._

  override val runsRightAfter : Option[String] = None
  override val runsAfter : List[String] = List("refchecks")

  val phaseName = "test!"

  def newPhase(previous : Phase) = new PluginPhase(previous)

  class PluginPhase(previous : Phase) extends StdPhase(previous) {
    def apply(unit : CompilationUnit) : Unit = {
      println("Phase ran !")
    }
  }
}

