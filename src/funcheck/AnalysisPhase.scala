package funcheck

import scala.tools.nsc._
import scala.tools.nsc.plugins._

class AnalysisComponent(val global: Global, pluginInstance: FunCheck) extends PluginComponent {
  import global._
  import global.definitions._

  // when we use 2.8.x, swap the following two lines
  val runsAfter = "refchecks"
  // override val runsRightAfter = "refchecks"

  val phaseName = pluginInstance.name

  def newPhase(prev: Phase) = new AnalysisPhase(prev)

  class AnalysisPhase(prev: Phase) extends StdPhase(prev) {
    def apply(unit: CompilationUnit): Unit = {
      (new ForeachTreeTraverser(findDefs)).traverse(unit.body)
      (new ForeachTreeTraverser(findEnsurings)).traverse(unit.body)


      if(pluginInstance.stopAfterAnalysis) {
        println("Analysis complete. Now terminating the compiler process.")
        exit(0)
      }
    }

    def findDefs(tree: Tree): Unit = tree match {
      case d: DefDef => println("Found a def! : " + d)
      case _ => ;
    }

    def findEnsurings(tree: Tree): Unit = tree match {
      case DefDef(/*mods*/ _, name, /*tparams*/ _, /*vparamss*/ _, /*tpt*/ _, 
        /* body */ 
        Apply(Select(Apply(TypeApply(Select(Select(This(scalaName), predefName), any2EnsuringName), TypeTree() :: Nil), body :: Nil), ensuringName), (anonymousFun @ Function(ValDef(_, resultName, resultType, EmptyTree) :: Nil, contractBody)) :: Nil) ) 
        if ( "scala".equals(scalaName.toString)
          && "Predef".equals(predefName.toString)
          && "any2Ensuring".equals(any2EnsuringName.toString)) => {
        println("Found a defdef with ensuring:")
        println("body: " + body)
        println("")
        println("cont: " + anonymousFun)
        println(resultName + " : " + resultType + " ==> " + contractBody)

      }

      case _ => ;

    }
  }
}
