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

class Synthesizer(val r: Reporter,
                  val solver: Solver,
                  generateDerivationTrees: Boolean = false,
                  filterFuns: Option[Set[String]]  = None,
                  firstOnly: Boolean               = false,
                  timeoutMs: Option[Long]          = None) {

  import r.{error,warning,info,fatalError}


  var derivationCounter = 1;

  def synthesize(p: Problem, rules: Set[Rule]): Solution = {

    val workList = new PriorityQueue[Task]()
    val rootTask = new RootTask(this, p)

    workList += rootTask

    val ts = System.currentTimeMillis

    def timeoutExpired(): Boolean = {
      timeoutMs match {
        case Some(t) if (System.currentTimeMillis-ts)/1000 > t => true
        case _ => false
      }
    }

    val worstSolution = Solution.choose(p)

    def bestSolutionSoFar(): Solution = {
      rootTask.solution.getOrElse(worstSolution)
    }
    
    while (!workList.isEmpty && !(firstOnly && rootTask.solution.isDefined)) {
      val task = workList.dequeue()

      val subProblems = task.run

      // Check if solving this task has the slightest chance of improving the
      // current solution
      if (task.minComplexity < bestSolutionSoFar().complexity) {
        if (!subProblems.isEmpty) {
          val name = Option(task.rule).map(_.name).getOrElse("root")
          println("["+name+"] Got: "+task.problem)
          println("["+name+"] Decomposed into:")
          for(p <- subProblems) {
            println("["+name+"]  - "+p)
          }
        }

        for (p <- subProblems; r <- rules) yield {
          workList += new Task(this, task, p, r)
        }
      }

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

  val rules = Rules.all(this) ++ Heuristics.all(this)

  import purescala.Trees._
  def synthesizeAll(program: Program): List[(Choose, Solution)] = {
    def noop(u:Expr, u2: Expr) = u

    var solutions = List[(Choose, Solution)]()

    def actOnChoose(f: FunDef)(e: Expr, a: Expr): Expr = e match {
      case ch @ Choose(vars, pred) =>
        val xs = vars
        val as = (variablesOf(pred)--xs).toList
        val phi = pred

        val sol = synthesize(Problem(as, phi, xs), rules)

        solutions = (ch -> sol) :: solutions

        a
      case _ =>
        a
    }

    // Look for choose()
    for (f <- program.definedFunctions.sortBy(_.id.toString) if f.body.isDefined) {
      if (filterFuns.isEmpty || filterFuns.get.contains(f.id.toString)) {
        treeCatamorphism(x => x, noop, actOnChoose(f), f.body.get)
      }
    }

    solutions.reverse
  }
}
