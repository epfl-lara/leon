package leon
package synthesis

class Task(
        val synth: Synthesizer, 
        val parent: Task,
        val rule: Rule,
        val problem: Problem,
        val subProblems: List[Problem],
        val onSuccess: List[Solution] => Solution,
        val score: Score
  ) extends Ordered[Task] {

  var subSolutions = Map[Problem, Solution]()

  def compare(that: Task) = this.score - that.score

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

  override def toString = description 

  def description = "by "+rule.name+"("+score+"): "+problem +" ⟿    "+subProblems.mkString(" ; ")
}

class RootTask(synth: Synthesizer, p: Problem) extends Task(synth, null, null, p, List(p), xs => xs.head, 0)
