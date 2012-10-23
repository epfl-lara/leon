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

    def applyRules(p: Problem, parent: Task): List[Task] = {
      rules.flatMap(_.isApplicable(p, parent))
    }

    val workList = new PriorityQueue[Task]()

    val rootTask = new RootTask(this, p)

    workList += rootTask

    solution = None

    while (!workList.isEmpty && solution.isEmpty) {
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
    task match {
      case rt: RootTask =>
        info(" SUCCESS!")
        this.solution = Some(solution)
      case t: Task =>
        info(" => Solved "+task.problem+" ⊢  "+solution)
        t.parent.subSucceeded(t.problem, solution)
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
        info(ScalaPrinter(sol.term))

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
