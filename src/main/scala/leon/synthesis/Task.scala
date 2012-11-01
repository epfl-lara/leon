package leon
package synthesis

abstract class Task(val synth: Synthesizer,
           val parent: Task,
           val problem: Problem,
           val priority: Priority) extends Ordered[Task] {

  def compare(that: Task) = this.priority - that.priority

  def run: List[Task]

  override def toString = " Task("+priority+"): " +problem
}

class SimpleTask(synth: Synthesizer,
                 override val parent: ApplyRuleTask,
                 problem: Problem,
                 priority: Priority) extends Task(synth, parent, problem, priority) {

  var solverTask: Option[ApplyRuleTask] = None
  var solution: Option[Solution] = None

  def solvedBy(t: ApplyRuleTask, s: Solution) {
    if (solution.map(_.score).getOrElse(-1) < s.score) {
      solution = Some(s)
      solverTask = Some(t)

      if (parent ne null) {
        parent.partlySolvedBy(this, s)
      }
    }
  }

  def run: List[Task] = {
    synth.rules.map(r => new ApplyRuleTask(synth, this, problem, r)).toList
  }

  var failed = Set[Rule]()
  def unsolvedBy(t: ApplyRuleTask) = {
    failed += t.rule
    if (failed.size == synth.rules.size) {
      val s = Solution.choose(problem)
      solution = Some(s)
      solverTask = None

      if (parent ne null) {
        parent.partlySolvedBy(this, s)
      }
    }
  }
}

class RootTask(synth: Synthesizer, problem: Problem) extends SimpleTask(synth, null, problem, 0)

class ApplyRuleTask(synth: Synthesizer,
                    override val parent: SimpleTask,
                    problem: Problem,
                    val rule: Rule) extends Task(synth, parent, problem, rule.priority) {

  var subTasks: List[SimpleTask]               = Nil
  var onSuccess: List[Solution] => Solution    = _
  var subSolutions : Map[SimpleTask, Solution] = _

  def partlySolvedBy(t: SimpleTask, s: Solution) {
    if (subSolutions.get(t).map(_.score).getOrElse(-1) < s.score) {
      subSolutions += t -> s

      if (subSolutions.size == subTasks.size) {
        val solution = onSuccess(subTasks map subSolutions)
        parent.solvedBy(this, solution)
      }
    }
  }

  def run: List[Task] = {
    rule.applyOn(this) match {
      case RuleSuccess(solution) =>
        // Solved
        parent.solvedBy(this, solution)
        Nil
      case RuleDecomposed(subProblems, onSuccess) =>
        this.subTasks     = subProblems.map(new SimpleTask(synth, this, _, 1000))
        this.onSuccess    = onSuccess
        this.subSolutions = Map()

        subTasks
      case RuleInapplicable =>
        parent.unsolvedBy(this)
        Nil
    }
  }

  override def toString = "Applying "+rule+" on "+problem
}
