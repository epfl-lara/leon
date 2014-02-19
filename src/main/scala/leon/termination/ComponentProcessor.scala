package leon
package termination

import purescala.TreeOps._
import purescala.Definitions._
import scala.collection.mutable.{Map => MutableMap}

class ComponentProcessor(checker: TerminationChecker) extends Processor(checker) {

  val name: String = "Component Processor"

  def run(problem: Problem) = {
    val pairs      : Set[(FunDef, FunDef)]    = checker.program.callGraph.filter({
      case (fd1, fd2) => problem.funDefs(fd1) && problem.funDefs(fd2)
    })
    val callGraph  : Map[FunDef,Set[FunDef]]  = pairs.groupBy(_._1).mapValues(_.map(_._2))
    val components : List[Set[FunDef]]        = ComponentBuilder.run(callGraph)
    val fdToSCC    : Map[FunDef, Set[FunDef]] = components.map(set => set.map(fd => fd -> set)).flatten.toMap

    val terminationCache : MutableMap[FunDef, Boolean] = MutableMap()
    def terminates(fd: FunDef) : Boolean = terminationCache.getOrElse(fd, {
      val scc = fdToSCC.getOrElse(fd, Set()) // functions that aren't called and don't call belong to no SCC
      val result = if (scc(fd)) false else scc.forall(terminates(_))
      terminationCache(fd) = result
      result
    })

    val terminating = problem.funDefs.filter(terminates(_))
    assert(components.forall(scc => (scc subsetOf terminating) || (scc intersect terminating).isEmpty))
    val newProblems = components.filter(scc => (scc intersect terminating).isEmpty).map(Problem(_))
    (terminating.map(Cleared(_)), newProblems)
  }
}
