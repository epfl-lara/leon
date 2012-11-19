package leon
package synthesis

import purescala.Common._
import purescala.Definitions.{Program, FunDef}
import purescala.TreeOps._
import purescala.Trees.{Expr, Not}
import purescala.ScalaPrinter
import sun.misc.{Signal, SignalHandler}

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

  var continue = true

  def synthesize(): Solution = {

    //val sigINT = new Signal("INT")
    //var oldHandler: SignalHandler = null
    //oldHandler = Signal.handle(sigINT, new SignalHandler {
    //  def handle(sig: Signal) {
    //    reporter.info("Aborting...")
    //    continue = false
    //    Signal.handle(sigINT, oldHandler)
    //  }
    //})

    /*
    if (generateDerivationTrees) {
      val deriv = new DerivationTree(rootTask)
      deriv.toDotFile("derivation"+derivationCounter+".dot")
      derivationCounter += 1
    }
    */

    val search = new AOSearch(problem, rules)

    val res = search.search

    println(res)

    Solution.none
  }


  import aographs._

  abstract class Task extends AOTask[Solution]
  case class TaskRunRule(problem: Problem, rule: Rule, app: RuleApplication) extends Task {
    val subSols = (1 to app.subProblemsCount).map {i => Solution.simplest }.toList
    val simpleSol = app.onSuccess(subSols)

    def cost = SolutionCost(simpleSol)

    def composeSolution(sols: List[Solution]): Solution = {
      app.onSuccess(sols)
    }
  }

  case class TaskTryRules(p: Problem) extends Task {
    def cost = ProblemCost(p)

    def composeSolution(sols: List[Solution]): Solution = {
      sys.error("Should not be called")
    }
  }

  class AOSearch(problem: Problem, rules: Set[Rule]) extends AndOrGraphSearch[Task, Solution](new AndOrGraph(TaskTryRules(problem))) {
    def processLeaf(l: g.Leaf) = {
      l.task match {
        case t: TaskTryRules =>
          val sub = rules.flatMap ( r => r.attemptToApplyOn(t.p).alternatives.map(TaskRunRule(t.p, r, _)) )

          if (!sub.isEmpty) {
            Expanded(sub.toList)
          } else {
            ExpandFailure
          }

        case t: TaskRunRule =>
          val prefix = "[%-20s] ".format(Option(t.rule).getOrElse("?"))

          info(prefix+"Got: "+t.problem)
          t.app.apply() match {
            case RuleSuccess(sol) =>
              info(prefix+"Solved with: "+sol)

              ExpandSuccess(sol)
            case RuleDecomposed(sub, onSuccess) =>
              info(prefix+"Got: "+t.problem)
              info(prefix+"Decomposed into:")
              for(p <- sub) {
                info(prefix+" - "+p)
              }

              Expanded(sub.map(TaskTryRules(_)))

            case RuleApplicationImpossible =>
              ExpandFailure
          }
      }
    }
  }
}


