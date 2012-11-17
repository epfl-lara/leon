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

    def currentDurationMs = System.currentTimeMillis-ts

    def timeoutExpired(): Boolean = {
      timeoutMs match {
        case Some(t) if currentDurationMs/1000 > t => true
        case _ => false
      }
    }

    var continue = true
    while (!workList.isEmpty && continue) {
      val task = workList.dequeue()

      val prefix = "[%-20s] ".format(Option(task.rule).map(_.toString).getOrElse("root"))

      if (!(firstOnly && (task.parent ne null) && task.parent.isSolved(task.problem))) {
        val subProblems = task.run()

        if (task.minComplexity <= bestSolutionSoFar.complexity) {
          if (task.solution.isDefined || !subProblems.isEmpty) {
            if (task.solution.isDefined) {
              info(prefix+"Got: "+task.problem)
              info(prefix+"Solved with: "+task.solution.get)
            } else {
              info(prefix+"Got: "+task.problem)
              info(prefix+"Decomposed into:")
              for(p <- subProblems) {
                info(prefix+" - "+p)
              }
            }
          }
          addProblems(task, subProblems)
        }
      }

      if (timeoutExpired()) {
        warning("Timeout reached")
        continue = false
      }
    }

    if (!workList.isEmpty) {
      // We flush the worklist by solving everything with chooses, that should
      // rebuild a partial solution
      while (!workList.isEmpty) {
        val t = workList.dequeue()

        if (t.parent ne null) {
          t.parent.partlySolvedBy(t, Solution.choose(t.problem))          
        }
      }
    }

    info("Finished in "+currentDurationMs+"ms")

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
