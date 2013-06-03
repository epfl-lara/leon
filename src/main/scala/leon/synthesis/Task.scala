/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis

/*
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
  var solver: Option[RuleApplication] = None

  var alternatives = Traversable[RuleApplication]()

  var minComplexity: AbsSolComplexity = new FixedSolComplexity(0)

  class TaskStep(val subProblems: List[Problem]) {
    var subSolutions = Map[Problem, Solution]()
    var subSolvers   = Map[Problem, Task]()
    var failures     = Set[Rule]()
  }

  class RuleApplication(
    val initProblems: List[Problem],
    val allNextSteps: List[List[Solution] => List[Problem]], 
    val onSuccess: List[Solution] => (Solution, Boolean)) {

    var allSteps    = List(new TaskStep(initProblems))
    var nextSteps   = allNextSteps
    def currentStep = allSteps.head

    def isSolvedFor(p: Problem) = allSteps.exists(_.subSolutions contains p) 

    def partlySolvedBy(t: Task, s: Solution) {
      if (currentStep.subProblems.contains(t.problem)) {
        if (isBetterSolutionThan(s, currentStep.subSolutions.get(t.problem))) {
          currentStep.subSolutions += t.problem -> s
          currentStep.subSolvers   += t.problem -> t

          if (currentStep.subSolutions.size == currentStep.subProblems.size) {
            val solutions = currentStep.subProblems map currentStep.subSolutions

            if (!nextSteps.isEmpty) {
              // Advance to the next step
              val newProblems = nextSteps.head.apply(solutions)
              nextSteps = nextSteps.tail

              synth.addProblems(Task.this, newProblems)

              allSteps = new TaskStep(newProblems) :: allSteps
            } else {
              onSuccess(solutions) match {
                case (s, true) =>
                  if (isBetterSolutionThan(s, solution)) {
                    solution = Some(s)
                    solver   = Some(this)

                    parent.partlySolvedBy(Task.this, s)
                  }
                case _ =>
                  // solution is there, but it is incomplete (precondition not strongest)
                  //parent.partlySolvedBy(this, Solution.choose(problem))
              }
            }
          }
        }
      }
    }

    val minComplexity: AbsSolComplexity = {
      val simplestSubSolutions = allNextSteps.foldLeft(initProblems.map(Solution.basic(_))){
        (sols, step) => step(sols).map(Solution.basic(_)) 
      }
      val simplestSolution = onSuccess(simplestSubSolutions)._1
      new FixedSolComplexity(parent.minComplexity.value + simplestSolution.complexity.value)
    }
  }

  // Is this subproblem already fixed?
  def isSolvedFor(problem: Problem): Boolean = parent.isSolvedFor(this.problem) || (alternatives.exists(_.isSolvedFor(problem)))

  def partlySolvedBy(t: Task, s: Solution) {
    alternatives.foreach(_.partlySolvedBy(t, s))
  }

  def run(): List[Problem] = {
    rule.applyOn(this) match {
      case RuleSuccess(solution) =>
        // Solved
        this.solution = Some(solution)
        parent.partlySolvedBy(this, solution)

        Nil

      case RuleAlternatives(xs) if xs.isEmpty =>
        // Inapplicable
        Nil

      case RuleAlternatives(steps) =>
        this.alternatives = steps.map( step => new RuleApplication(step.subProblems, step.interSteps, step.onSuccess) )

        this.alternatives.flatMap(_.initProblems).toList
    }
  }

  override def toString = "Applying "+rule+" on "+problem
}

class RootTask(synth: Synthesizer, problem: Problem) extends Task(synth, null, problem, null) {
  var solverTask: Option[Task] = None

  override def run() = {
    List(problem)
  }

  override def isSolvedFor(problem: Problem) = solverTask.isDefined

  override def partlySolvedBy(t: Task, s: Solution) {
    if (isBetterSolutionThan(s, solution)) {
      solution   = Some(s)
      solverTask = Some(t)
    }
  }
}
*/
