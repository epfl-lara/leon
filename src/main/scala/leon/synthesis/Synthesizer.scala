package leon
package synthesis

import purescala.Common._
import purescala.Definitions.Program
import purescala.Trees.{Expr, Not}

import Extensions.Solver

import collection.mutable.PriorityQueue

class Synthesizer(val r: Reporter, val solvers: List[Solver]) {
  import r.{error,warning,info,fatalError}

  private[this] var solution: Solution = null

  def synthesize(p: Problem, rules: List[Rule]): Solution = {

    def applyRules(p: Problem, parent: Task): List[Task] = {
      rules.flatMap(_.isApplicable(p, parent))
    }

    val workList = new PriorityQueue[Task]()

    val rootTask = new RootTask(this, p)

    workList += rootTask

    while (!workList.isEmpty) {
      val task = workList.dequeue()

      task.subProblems match {
        case Nil =>
          throw new Exception("Such tasks shouldbe handled immediately")
        case subProblems =>
          for (sp <- subProblems) {
            info("Now handling: "+sp)

            val alternatives = applyRules(sp, task)

            alternatives.find(_.isSuccess) match {
              case Some(ss) =>
                info(" => Success!")
                ss.succeeded()
              case None =>
                workList ++= alternatives
            }

            // We are stuck
            if (alternatives.isEmpty) {
              // I give up
              val sol = Solution.choose(sp)
              warning(" => Solved (by choose): "+sp+" ⊢  "+sol)
              task.subSucceeded(sp, sol)
            } else {
              info(" => Possible Next Steps:")
              alternatives.foreach(t => info(" -   "+t.description))
            }
          }
      }

    }

    solution
  }

  def solveSAT(phi: Expr): (Option[Boolean], Map[Identifier, Expr]) = {
    for (s <- solvers) {
      s.solveOrGetCounterexample(Not(phi)) match {
        case (Some(true), _) =>
          return (Some(false), Map())
        case (Some(false), model) =>
          return (Some(true), model)
        case _ =>
      }
    }
    (None, Map())
  }

  def onTaskSucceeded(task: Task, solution: Solution) {
    info(" => Solved "+task.problem+" ⊢  "+solution)
    task match {
      case rt: RootTask =>
        info(" SUCCESS!")
        this.solution = solution
      case t: Task =>
        t.parent.subSucceeded(t.problem, solution)
    }
  }

  def test() {
    import purescala.Common._
    import purescala.Trees._
    import purescala.TypeTrees._

    val x = Variable(FreshIdentifier("x").setType(Int32Type))
    val y = Variable(FreshIdentifier("y").setType(Int32Type))
    val p = Problem(Nil, And(List(GreaterThan(x, y), Equals(y, IntLiteral(2)), Equals(x, IntLiteral(3)))), List(x.id, y.id))

    synthesize(p, Rules.all(this))
  }

  def synthesizeAll(program: Program) = {
    solvers.foreach(_.setProgram(program))
    program
  }
}
