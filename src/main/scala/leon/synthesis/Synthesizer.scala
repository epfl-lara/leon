package leon
package synthesis

import purescala.Common._
import purescala.Definitions.{Program, FunDef}
import purescala.Trees.{Expr, Not}
import purescala.ScalaPrinter

import Extensions.Solver

import collection.mutable.PriorityQueue

class Synthesizer(val r: Reporter, val solvers: List[Solver]) {
  import r.{error,warning,info,fatalError}

  private[this] var solution: Option[Solution] = None

  def synthesize(p: Problem, rules: List[Rule]): Solution = {

    val workList = new PriorityQueue[Task]()
    val rootTask = new RootTask(this, p)

    workList += rootTask
    solution = None

    while (!workList.isEmpty && solution.isEmpty) {
      val task = workList.dequeue()

      info("Now handling: "+task.problem)

      val alternatives = rules.flatMap(_.isApplicable(task))

      alternatives.find(_.isSuccess) match {
        case Some(ss) =>
          info(" => "+ss.rule+" succeeded")
          ss.succeeded()
        case None =>
          info(" => Possible Next Steps:")
          alternatives.foreach(t => info(" -   "+t.description))
          workList ++= alternatives.flatMap(_.subTasks)
      }

      // We are stuck
      if (alternatives.isEmpty) {
        val sol = Solution.choose(task.problem)
        warning(" => I give up: "+task.problem+" ⊢  "+sol)
        onTaskSucceeded(task, sol)
      }
    }

    solution.getOrElse(Solution.none)
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
    if (task.parent eq null) {
      info(" SUCCESS!")
      this.solution = Some(solution)
    } else {
      task.parent.subSucceeded(task.problem, solution)
    }
  }

  def synthesizeAll(program: Program) = {
    import purescala.Trees._

    solvers.foreach(_.setProgram(program))

    val rules = Rules.all(this)

    def noop(u:Expr, u2: Expr) = u

    def actOnChoose(f: FunDef)(e: Expr, a: Expr): Expr = e match {
      case Choose(vars, pred) =>
        val xs = vars
        val as = (variablesOf(pred)--xs).toList
        val phi = pred

        info("")
        info("")
        info("In Function "+f.id+":")
        info("-"*80)
        val sol = synthesize(Problem(as, phi, xs), rules)

        info("Scala code:")
        info(ScalaPrinter(IfExpr(sol.pre, sol.term, Error("Precondition failed").setType(sol.term.getType))))

        a
      case _ =>
        a
    }

    // Look for choose()
    for (f <- program.definedFunctions.sortBy(_.id.toString) if f.body.isDefined) {
      treeCatamorphism(x => x, noop, actOnChoose(f), f.body.get)
    }

    program
  }
}
