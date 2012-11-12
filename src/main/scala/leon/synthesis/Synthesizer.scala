package leon
package synthesis

import purescala.Common._
import purescala.Definitions.{Program, FunDef}
import purescala.TreeOps._
import purescala.Trees.{Expr, Not}
import purescala.ScalaPrinter

import solvers.Solver
import java.io.File

import collection.mutable.PriorityQueue

class Synthesizer(val reporter: Reporter,
                  val solver: Solver,
                  val problem: Problem,
                  val ruleConstructors: Set[Synthesizer => Rule],
                  generateDerivationTrees: Boolean = false,
                  filterFuns: Option[Set[String]]  = None,
                  firstOnly: Boolean               = false,
                  timeoutMs: Option[Long]          = None) {
  import reporter.{error,warning,info,fatalError}

  val rules = ruleConstructors.map(_.apply(this))

  var derivationCounter = 1;

  val rootTask: RootTask = new RootTask(this, problem)

  val workList = new PriorityQueue[Task]()

  def bestSolutionSoFar(): Solution = {
    rootTask.solution.getOrElse(worstSolution)
  }

  val worstSolution = Solution.choose(problem)

  def synthesize(): Solution = {
    workList.clear()
    workList += rootTask

    val ts = System.currentTimeMillis

    def timeoutExpired(): Boolean = {
      timeoutMs match {
        case Some(t) if (System.currentTimeMillis-ts)/1000 > t => true
        case _ => false
      }
    }

    while (!workList.isEmpty && !(firstOnly && rootTask.solution.isDefined)) {
      val task = workList.dequeue()

      task.run()

      if (timeoutExpired()) {
        warning("Timeout reached")
        workList.clear()
      }
    }

    if (generateDerivationTrees) {
      val deriv = new DerivationTree(rootTask)
      deriv.toDotFile("derivation"+derivationCounter+".dot")
      derivationCounter += 1
    }

    bestSolutionSoFar()
  }

  def addProblems(task: Task, problems: Traversable[Problem]) {
    // Check if solving this task has the slightest chance of improving the
    // current solution
    for (p <- problems; rule <- rules) yield {
      workList += new Task(this, task, p, rule)
    }
  }
}
