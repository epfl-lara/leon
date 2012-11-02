package leon
package synthesis

class Task(synth: Synthesizer,
           val parent: Task,
           val problem: Problem,
           val rule: Rule) extends Ordered[Task] {

  val complexity: TaskComplexity = new TaskComplexity(this)

  def compare(that: Task) = that.complexity compare this.complexity // sort by complexity ASC

  var subProblems: List[Problem]               = Nil
  var onSuccess: List[Solution] => Solution    = _
  var subSolutions : Map[Problem, Solution]    = Map()
  var subSolvers : Map[Problem, Task]          = Map()
  var solution : Option[Solution]              = None

  def isBetterSolutionThan(sol: Solution, osol: Option[Solution]): Boolean =
    osol match {
      case Some(s) => s.complexity > sol.complexity
      case None => true
    }

  def partlySolvedBy(t: Task, s: Solution) {
    if (isBetterSolutionThan(s, subSolutions.get(t.problem))) {
      subSolutions += t.problem -> s
      subSolvers   += t.problem -> t

      if (subSolutions.size == subProblems.size) {
        solution = Some(onSuccess(subProblems map subSolutions))
        parent.partlySolvedBy(this, solution.get)
      }
    }
  }

  var failures = Set[Rule]()
  def unsolvedBy(t: Task) {
    failures += t.rule

    if (failures.size == synth.rules.size) {
      // We might want to report unsolved instead of solvedByChoose, depending
      // on the cases
      parent.partlySolvedBy(this, Solution.choose(problem))
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
        parent.unsolvedBy(this)
        Nil
    }
  }

  lazy val minSolutionCost: Cost = rule.cost + parent.minSolutionCost

  override def toString = "Applying "+rule+" on "+problem
}

class RootTask(synth: Synthesizer, problem: Problem) extends Task(synth, null, problem, null) {
  var solver: Option[Task] = None

  override lazy val minSolutionCost = 0

  override def partlySolvedBy(t: Task, s: Solution) {
    if (isBetterSolutionThan(s, solution)) {
      solution = Some(s)
      solver   = Some(t)
    }
  }

  override def unsolvedBy(t: Task) {
    failures += t.rule

    if (failures.size == synth.rules.size) {
      // We might want to report unsolved instead of solvedByChoose, depending
      // on the cases
      solution = Some(Solution.choose(problem))
      solver   = None
    }
  }

  override def run: List[Problem] = {
    List(problem)
  }
}
