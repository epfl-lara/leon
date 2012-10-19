package leon
package synthesis

import purescala.Definitions.Program

import collection.mutable.PriorityQueue

class Synthesizer(rules: List[Rule]) {
  def this() = this(Rules.all)


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

    println
    println(" ++ RESULT ++ ")
    println("==> "+p+" ⊢  "+solution)

    solution
  }

  def test1 = {
    import purescala.Common._
    import purescala.Trees._
    import purescala.TypeTrees._

    val aID = FreshIdentifier("a").setType(Int32Type)
    val a = Variable(aID)
    val p = Problem(Nil, And(GreaterThan(a, IntLiteral(2)), Equals(a, IntLiteral(3))), List(aID))

    synthesize(p)
  }

  def synthesizeAll(p: Program): Program = {
    test1
    p
  }
}

