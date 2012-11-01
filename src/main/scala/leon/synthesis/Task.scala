package leon
package synthesis

class Task(synth: Synthesizer,
           parent: Task,
           val problem: Problem,
           val rule: Rule) extends Ordered[Task] {

  def compare(that: Task) = this.complexity compare that.complexity

  def complexity = Complexity.max

  var subProblems: List[Problem]               = Nil
  var onSuccess: List[Solution] => Solution    = _
  var subSolutions : Map[Problem, Solution]    = _
  var subSolvers : Map[Problem, Task]          = _

  def currentComplexityFor(p: Problem): Complexity =
    subSolutions.get(p) match {
      case Some(s) => s.complexity
      case None => Complexity.max
    }

  def partlySolvedBy(t: Task, s: Solution) {
    if (s.complexity < currentComplexityFor(t.problem)) {
      subSolutions += t.problem -> s
      subSolvers   += t.problem -> t

      if (subSolutions.size == subProblems.size) {
        val solution = onSuccess(subProblems map subSolutions)
        parent.partlySolvedBy(this, solution)
      }
    }
  }

  def run: List[Task] = {
    rule.applyOn(this) match {
      case RuleSuccess(solution) =>
        // Solved
        parent.partlySolvedBy(this, solution)
        Nil
      case RuleDecomposed(subProblems, onSuccess) =>
        this.subProblems  = subProblems
        this.onSuccess    = onSuccess
        this.subSolutions = Map()
        this.subSolvers   = Map()

        for (p <- subProblems; r <- synth.rules) yield {
          new Task(synth, this, p, r)
        }
      case RuleInapplicable =>
        Nil
    }
  }

  override def toString = "Applying "+rule+" on "+problem
}

class RootTask(synth: Synthesizer, problem: Problem) extends Task(synth, null, problem, null) {
  var solution: Option[Solution]    = None
  var solver: Option[Task] = None

  override def partlySolvedBy(t: Task, s: Solution) = {
    if (s.complexity < solution.map(_.complexity).getOrElse(Complexity.max)) {
      solution = Some(s)
      solver   = Some(t)
    }
  }

  override def run: List[Task] = {
    for (r <- synth.rules.toList) yield {
      new Task(synth, this, problem, r)
    }
  }
}
