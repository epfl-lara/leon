package leon
package synthesis

class Task(val synth: Synthesizer,
           val parent: DecomposedTask,
           val problem: Problem,
           val score: Score) extends Ordered[Task] {

  def compare(that: Task) = this.score - that.score

  override def toString = "("+score+") " +problem
}

class DecomposedTask(synth: Synthesizer,
                     parent: DecomposedTask,
                     problem: Problem,
                     score: Score,
                     val rule: Rule,
                     val subProblems: List[Problem],
                     val onSuccess: List[Solution] => Solution) extends Task(synth, parent, problem, score) {

  def subTasks = subProblems.map(new Task(synth, this, _, score))

  var subSolutions = Map[Problem, Solution]()

  def isSuccess = subProblems.isEmpty

  def succeeded() {
    assert(isSuccess)

    val solution = onSuccess(Nil)

    synth.onTaskSucceeded(this, solution)
  }

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

  def description = "by "+rule.name+"("+score+"): "+problem +" ⟿    "+subProblems.mkString(" ; ")
}

class RootTask(synth: Synthesizer, p: Problem) extends Task(synth, null, p, 0)
