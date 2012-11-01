package leon
package synthesis

import purescala.Common._
import purescala.Definitions.{Program, FunDef}
import purescala.TreeOps._
import purescala.Trees.{Expr, Not}
import purescala.ScalaPrinter

import solvers.Solver
import java.io.File

import collection.mutable.PriorityQueue

class Synthesizer(val r: Reporter,
                  val solvers: List[Solver],
                  generateDerivationTrees: Boolean,
                  filterFuns: Option[Set[String]],
                  firstOnly: Boolean) {

  import r.{error,warning,info,fatalError}


  var derivationCounter = 1;

  def synthesize(p: Problem, rules: Set[Rule]): Solution = {

    val workList = new PriorityQueue[Task]()
    val rootTask = new RootTask(this, p)


    workList += rootTask

    while (!workList.isEmpty && !(firstOnly && rootTask.solution.isDefined)) {
      val task = workList.dequeue()

      val subtasks = task.run

      workList ++= subtasks
    }

    if (generateDerivationTrees) {
      val deriv = new DerivationTree(rootTask)
      deriv.toDotFile("derivation"+derivationCounter+".dot")
      derivationCounter += 1
    }

    rootTask.solution.getOrElse(Solution.none)
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

  val rules = Rules.all(this) ++ Heuristics.all(this)

  import purescala.Trees._
  def synthesizeAll(program: Program): List[(Choose, Solution)] = {

    solvers.foreach(_.setProgram(program))


    def noop(u:Expr, u2: Expr) = u

    var solutions = List[(Choose, Solution)]()

    def actOnChoose(f: FunDef)(e: Expr, a: Expr): Expr = e match {
      case ch @ Choose(vars, pred) =>
        val xs = vars
        val as = (variablesOf(pred)--xs).toList
        val phi = pred

        val sol = synthesize(Problem(as, phi, xs), rules)

        solutions = (ch -> sol) :: solutions

        a
      case _ =>
        a
    }

    // Look for choose()
    for (f <- program.definedFunctions.sortBy(_.id.toString) if f.body.isDefined) {
      if (filterFuns.isEmpty || filterFuns.get.contains(f.id.toString)) {
        treeCatamorphism(x => x, noop, actOnChoose(f), f.body.get)
      }
    }

    solutions.reverse
  }
}
