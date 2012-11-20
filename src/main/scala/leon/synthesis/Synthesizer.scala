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

import synthesis.search._

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

    val search = new AOSearch(problem, rules)

    val sigINT = new Signal("INT")
    var oldHandler: SignalHandler = null
    oldHandler = Signal.handle(sigINT, new SignalHandler {
      def handle(sig: Signal) {
        println
        reporter.info("Aborting...")

        continue = false
        search.continue = false

        Signal.handle(sigINT, oldHandler)
      }
    })

    val ts = System.currentTimeMillis()

    val res = search.search()

    val diff = System.currentTimeMillis()-ts
    reporter.info("Finished in "+diff+"ms")

    /*
    if (generateDerivationTrees) {
      val deriv = new DerivationTree(rootTask)
      deriv.toDotFile("derivation"+derivationCounter+".dot")
      derivationCounter += 1
    }
    */

    new AndOrGraphDotConverter(search.g).writeFile("test.dot")

    res.getOrElse(Solution.choose(problem))
  }

  case class TaskRunRule(problem: Problem, rule: Rule, app: RuleApplication) extends AOAndTask[Solution] {
    def cost = RuleApplicationCost(rule, app)

    def composeSolution(sols: List[Solution]): Solution = {
      app.onSuccess(sols)
    }

    override def toString = rule.name
  }

  case class TaskTryRules(p: Problem) extends AOOrTask[Solution] {
    def cost = ProblemCost(p)

    override def toString = p.toString
  }

  class AOSearch(problem: Problem,
                 rules: Set[Rule]) extends AndOrGraphSearch[TaskRunRule, TaskTryRules, Solution](new AndOrGraph(TaskTryRules(problem))) {

    def processAndLeaf(t: TaskRunRule) = {
      val prefix = "[%-20s] ".format(Option(t.rule).getOrElse("?"))

      t.app.apply() match {
        case RuleSuccess(sol) =>
          info(prefix+"Got: "+t.problem)
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
          ExpandFailure()
      }
    }

    def processOrLeaf(t: TaskTryRules) = {
      val sub = rules.flatMap ( r => r.attemptToApplyOn(t.p).alternatives.map(TaskRunRule(t.p, r, _)) )

      if (!sub.isEmpty) {
        Expanded(sub.toList)
      } else {
        ExpandFailure()
      }
    }
  }
}


