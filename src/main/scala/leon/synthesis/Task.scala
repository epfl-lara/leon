package leon
package synthesis

class Task(synth: Synthesizer,
           val parent: Task,
           val problem: Problem,
           val rule: Rule) extends Ordered[Task] {

  def compare(that: Task) = {
    val cproblem = -(this.problem.complexity compare that.problem.complexity) // problem DESC

    if (cproblem == 0) {
      // On equal complexity, order tasks by rule priority
      this.rule.priority-that.rule.priority
    } else {
      cproblem
    }
  }

  def isBetterSolutionThan(sol: Solution, osol: Option[Solution]): Boolean = {
    osol match {
      case Some(s) => s.complexity > sol.complexity
      case None => true
    }
  }

  var solution: Option[Solution] = None
  var minComplexity: AbsSolComplexity = new FixedSolComplexity(0)

  class TaskStep(val subProblems: List[Problem]) {
    var subSolutions = Map[Problem, Solution]()
    var subSolvers   = Map[Problem, Task]()
    var failures     = Set[Rule]()
  }

  var steps: List[TaskStep]                            = Nil
  var nextSteps: List[List[Solution] => List[Problem]] = Nil
  var onSuccess: List[Solution] => Solution            = _

  def currentStep                 = steps.head

  def partlySolvedBy(t: Task, s: Solution) {
    if (isBetterSolutionThan(s, currentStep.subSolutions.get(t.problem))) {
      currentStep.subSolutions += t.problem -> s
      currentStep.subSolvers   += t.problem -> t

      if (currentStep.subSolutions.size == currentStep.subProblems.size) {
        val solutions = currentStep.subProblems map currentStep.subSolutions

        if (!nextSteps.isEmpty) {
          val newProblems = nextSteps.head.apply(solutions)
          nextSteps = nextSteps.tail

          synth.addProblems(this, newProblems)

          steps = new TaskStep(newProblems) :: steps
        } else {
          solution = Some(onSuccess(solutions))
          parent.partlySolvedBy(this, solution.get)
        }
      }
    }
  }

  def unsolvedBy(t: Task) {
    currentStep.failures += t.rule

    if (currentStep.failures.size == synth.rules.size) {
      // We might want to report unsolved instead of solvedByChoose, depending
      // on the cases
      parent.partlySolvedBy(this, Solution.choose(problem))
    }
  }

  def run(): List[Problem] = {
    rule.applyOn(this) match {
      case RuleSuccess(solution) =>
        // Solved
        this.solution = Some(solution)
        parent.partlySolvedBy(this, solution)

        val prefix = "[%-20s] ".format(Option(rule).map(_.toString).getOrElse("root"))
        println(prefix+"Got: "+problem)
        println(prefix+"Solved with: "+solution)
        Nil

      case RuleMultiSteps(subProblems, interSteps, onSuccess) =>
        this.steps = new TaskStep(subProblems) :: Nil
        this.nextSteps = interSteps
        this.onSuccess = onSuccess

        // Compute simplest solution possible to evaluate whether this rule is worth it
        // To each problem we assign the most basic solution, fold on all inner
        // steps, and then reconstruct final solution
        val simplestSubSolutions  = interSteps.foldLeft(subProblems.map(Solution.basic(_))){ (sols, step) => step(sols).map(Solution.basic(_)) }
        val simplestSolution = onSuccess(simplestSubSolutions)
        minComplexity = new FixedSolComplexity(parent.minComplexity.value + simplestSolution.complexity.value)
        val prefix = "[%-20s] ".format(Option(rule).map(_.toString).getOrElse("root"))
        println(prefix+"Got: "+problem)
        println(prefix+"Decomposed into:")
        for(p <- subProblems) {
          println(prefix+" - "+p)
        }

        subProblems

      case RuleInapplicable =>
        parent.unsolvedBy(this)
        Nil
    }
  }

  override def toString = "Applying "+rule+" on "+problem
}

class RootTask(synth: Synthesizer, problem: Problem) extends Task(synth, null, problem, null) {
  var solver: Option[Task] = None

  override def run() = {
    List(problem)
  }

  override def partlySolvedBy(t: Task, s: Solution) {
    solution = Some(s)
    solver   = Some(t)
  }

  override def unsolvedBy(t: Task) {
  }

}
