package leon
package synthesis

class Task(
        val parent: Task,
        val problem: Problem,
        val subProblems: List[Problem],
        val construct: List[Solution] => Solution,
        val score: Score
  ) extends Ordered[Task] {

  var subSolutions = Map[Problem, Solution]()

  def compare(that: Task) = this.score - that.score

  def isSuccess = subProblems.isEmpty

  def onSuccess() {
    assert(isSuccess)
    notifyParent(construct(Nil))
  }

  def onSuccess(p: Problem, s: Solution) {
    assert(subProblems contains p)
    assert(!(subSolutions contains p))

    subSolutions += p -> s

    if (subSolutions.size == subProblems.size) {

      val solution = construct(subProblems map subSolutions) 

      println(": "+problem+" ⊢  "+solution)

      notifyParent(solution)
    }
  }

  def notifyParent(solution: Solution) {
    parent.onSuccess(problem, solution)
  }
}

class RootTask(p: Problem) extends Task(null, p, List(p), xs => xs.head, 0) {
  override def notifyParent(solution: Solution) {
    sys.error("You need to extend this!")
  }
}
