package leon
package synthesis

class Task(
        val parent: Task,
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

    println("Found solution: "+problem+" ⊢  "+solution)

    notifyParent(solution)
  }

  def subSucceeded(p: Problem, s: Solution) {
    assert(subProblems contains p)
    assert(!(subSolutions contains p))

    subSolutions += p -> s

    if (subSolutions.size == subProblems.size) {

      val solution = onSuccess(subProblems map subSolutions) 

      println("Found solution: "+problem+" ⊢  "+solution)

      notifyParent(solution)
    }
  }

  def notifyParent(solution: Solution) {
    parent.subSucceeded(problem, solution)
  }
}

class RootTask(p: Problem) extends Task(null, p, List(p), xs => xs.head, 0) {
  override def notifyParent(solution: Solution) {
    sys.error("You need to override this!")
  }
}
