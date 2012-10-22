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
                info(" => Possible Next Steps:")
                alternatives.foreach(t => info(" -   "+t.description))
                workList ++= alternatives
            }

            // We are stuck
            if (alternatives.isEmpty) {
              // I give up
              val sol = Solution.choose(sp)
              warning(" => Solved (by choose): "+sp+" ⊢  "+sol)
              task.subSucceeded(sp, sol)
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
    task match {
      case rt: RootTask =>
        info(" SUCCESS!")
        this.solution = solution
      case t: Task =>
        info(" => Solved "+task.problem+" ⊢  "+solution)
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
    import purescala.Trees._

    solvers.foreach(_.setProgram(program))

    val rules = Rules.all(this)

    def noop(u:Expr, u2: Expr) = u

    def actOnChoose(e: Expr, a: Expr): Expr = e match {
      case Choose(vars, pred) =>
        val xs = vars
        val as = (variablesOf(pred)--xs).toList
        val phi = pred

        synthesize(Problem(as, phi, xs), rules)

        a
      case _ =>
        a
    }

    // Look for choose()
    for (f <- program.definedFunctions if f.body.isDefined) {
      println(f)
      treeCatamorphism(x => x, noop, actOnChoose, f.body.get)
    }

    program
  }
}
