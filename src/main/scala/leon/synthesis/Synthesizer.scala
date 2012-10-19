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
          throw new Exception("Such tasks shouldbe handled immediately")
        case subProblems =>
          for (sp <- subProblems) {
            val alternatives = applyRules(sp, task)

            alternatives.find(_.isSuccess) match {
              case Some(ss) =>
                ss.onSuccess()
              case None =>
                workList ++= alternatives
            }

            // We are stuck
            if (alternatives.isEmpty) {
              // I give up
              task.onSuccess(sp, Solution.choose(sp))
            }
          }
      }

    }

    solution
  }
}

