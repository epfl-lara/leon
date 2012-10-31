package leon
package synthesis

abstract class Task(val synth: Synthesizer,
           val parent: Task,
           val problem: Problem,
           val priority: Priority) extends Ordered[Task] {

  def compare(that: Task) = this.priority - that.priority

  /*
  def decompose(rule: Rule, subProblems: List[Problem], onSuccess: List[Solution] => Solution, score: Score): DecomposedTask = {
    new DecomposedTask(this.synth, this.parent, this.problem, score, rule, subProblems, onSuccess)
  }

  def solveUsing(rule: Rule, onSuccess: => Solution, score: Score): DecomposedTask = {
    new DecomposedTask(this.synth, this.parent, this.problem, 1000, rule, Nil, { case _ => onSuccess })
  }
  */

  def run: List[Task]

  override def toString = " Task("+priority+"): " +problem
}

class SimpleTask(synth: Synthesizer,
                 override val parent: ApplyRuleTask,
                 problem: Problem,
                 priority: Priority) extends Task(synth, parent, problem, priority) {

  def succeeded(solution: Solution) {
    synth.onTaskSucceeded(this, solution)
  }

  def run: List[Task] = {
    synth.rules.map(r => new ApplyRuleTask(synth, this, problem, priority, r))
  }

  var failed = Set[Rule]()
  def notifyInapplicable(r: Rule) = {
    failed += r
    if (failed.size == synth.rules.size) {
      synth.onTaskSucceeded(this, Solution.choose(problem))
    }
  }
}

class RootTask(synth: Synthesizer, problem: Problem) extends SimpleTask(synth, null, problem, 0)

class ApplyRuleTask(synth: Synthesizer,
                    override val parent: SimpleTask,
                    problem: Problem,
                    priority: Priority,
                    val rule: Rule) extends Task(synth, parent, problem, priority) {

  var subProblems: List[Problem]            = _
  var onSuccess: List[Solution] => Solution = _
  var subSolutions : Map[Problem, Solution] = _

  def subSucceeded(p: Problem, s: Solution) {
    assert(subProblems contains p, "Problem "+p+" is unknown to me ?!?")

    if (subSolutions.get(p).map(_.score).getOrElse(-1) < s.score) {
      subSolutions += p -> s

      if (subSolutions.size == subProblems.size) {

        val solution = onSuccess(subProblems map subSolutions)

        synth.onTaskSucceeded(this, solution)
      }
    }
  }

  def run: List[Task] = {
    rule.applyOn(this) match {
      case RuleSuccess(solution) =>
        // Solved
        synth.onTaskSucceeded(this, solution)
        Nil
      case RuleDecomposed(subProblems, onSuccess) =>
        this.subProblems  = subProblems
        this.onSuccess    = onSuccess
        this.subSolutions = Map()

        subProblems.map(new SimpleTask(synth, this, _, 42))
      case RuleInapplicable =>
        parent.notifyInapplicable(rule)
        Nil
    }
  }

  override def toString = "Trying "+rule+" on "+problem
}
