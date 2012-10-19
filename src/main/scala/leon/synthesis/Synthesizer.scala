package leon
package synthesis

import collection.mutable.PriorityQueue

class Synthesizer(rules: List[Rule]) {
  def applyRules(p: Problem, parent: Task): List[Task] = {
    rules.flatMap(_.isApplicable(p, parent))
  }

  def synthesize(p: Problem): Solution = {
    val workList = new PriorityQueue[Task]()

    var solution: Solution = null

    val rootTask = new RootTask(p) {
      override def notifyParent(s: Solution) {
        solution = s
      }
    }

    workList += rootTask

    while (!workList.isEmpty) {
      val task = workList.dequeue()

      task.subProblems match {
        case Nil =>
          task.onSuccess()
        case subProblems =>
          workList ++= subProblems.flatMap(applyRules(_, task))
      }

    }

    solution
  }
}

