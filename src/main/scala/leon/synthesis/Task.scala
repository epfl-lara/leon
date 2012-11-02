package leon
package synthesis

class Task(synth: Synthesizer,
           parent: Task,
           val problem: Problem,
           val rule: Rule) extends Ordered[Task] {

  def compare(that: Task) = -(this.complexity compare that.complexity) // sort by complexity ASC

  val complexity = new TaskComplexity(problem, Option(rule))

  var subProblems: List[Problem]               = Nil
  var onSuccess: List[Solution] => Solution    = _
  var subSolutions : Map[Problem, Solution]    = Map()
  var subSolvers : Map[Problem, Task]          = Map()
  var solution : Option[Solution]              = None

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
        solution = Some(onSuccess(subProblems map subSolutions))
        parent.partlySolvedBy(this, solution.get)
      }
    }
  }

  def run: List[Problem] = {
    rule.applyOn(this) match {
      case RuleSuccess(solution) =>
        // Solved
        this.solution = Some(solution)
        parent.partlySolvedBy(this, solution)
        Nil

      case RuleDecomposed(subProblems, onSuccess) =>
        this.subProblems  = subProblems
        this.onSuccess    = onSuccess
        subProblems

      case RuleInapplicable =>
        Nil
    }
  }

  override def toString = "Applying "+rule+" on "+problem
}

class RootTask(synth: Synthesizer, problem: Problem) extends Task(synth, null, problem, null) {
  var solver: Option[Task] = None

  override def partlySolvedBy(t: Task, s: Solution) = {
    if (s.complexity < solution.map(_.complexity).getOrElse(Complexity.max)) {
      solution = Some(s)
      solver   = Some(t)
    }
  }

  override def run: List[Problem] = {
    List(problem)
  }
}
