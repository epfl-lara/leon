package leon
package synthesis

import synthesis.search._

case class TaskRunRule(problem: Problem, rule: Rule, app: RuleApplication) extends AOAndTask[Solution] {
  val cost = RuleApplicationCost(rule, app)

  def composeSolution(sols: List[Solution]): Solution = {
    app.onSuccess(sols)
  }

  override def toString = rule.name
}

case class TaskTryRules(p: Problem) extends AOOrTask[Solution] {
  val cost = ProblemCost(p)

  override def toString = p.toString
}

class SimpleSearch(synth: Synthesizer,
                   problem: Problem,
                   rules: Set[Rule]) extends AndOrGraphSearch[TaskRunRule, TaskTryRules, Solution](new AndOrGraph(TaskTryRules(problem))) {

  import synth.reporter._

  val sctx = SynthesisContext.fromSynthesizer(synth)

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
    val sub = rules.flatMap ( r => r.attemptToApplyOn(sctx, t.p).alternatives.map(TaskRunRule(t.p, r, _)) )

    if (!sub.isEmpty) {
      Expanded(sub.toList)
    } else {
      ExpandFailure()
    }
  }
}
