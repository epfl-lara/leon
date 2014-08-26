/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import purescala.Common._
import purescala.Definitions.{Program, FunDef, ModuleDef, DefType}
import purescala.TreeOps._
import purescala.Trees._
import purescala.ScalaPrinter

import solvers._
import solvers.combinators._
import solvers.z3._

import java.io.File

import synthesis.search._

class Synthesizer(val context : LeonContext,
                  val functionContext: Option[FunDef],
                  val program: Program,
                  val problem: Problem,
                  val options: SynthesisOptions) {

  val reporter = context.reporter

  def synthesize(): (Solution, Boolean) = {

    val search = if (options.manualSearch) {
        new ManualSearch(this, problem)
      } else if (options.searchWorkers > 1) {
        new ParallelSearch(this, problem, options.searchWorkers)
      } else {
        options.searchBound match {
          case Some(b) =>
            new BoundedSearch(this, problem, b)

          case None =>
            new SimpleSearch(this, problem)
        }
      }

    val t = context.timers.synthesis.search.start()

    val res = search.search()

    val diff = t.stop()
    reporter.info("Finished in "+diff+"ms")

    if (options.generateDerivationTrees) {
      val converter = new AndOrGraphDotConverter(search.g, options.firstOnly)
      converter.writeFile("derivation"+AndOrGraphDotConverterCounter.next()+".dot")
    }

    res match {
      case Some((solution, true)) =>
        (solution, true)
      case Some((sol, false)) =>
        validateSolution(search, sol, 5000L)
      case None =>
        (new AndOrGraphPartialSolution(search.g, (task: TaskRunRule) => Solution.choose(task.problem), true).getSolution, false)
    }
  }

  def validateSolution(search: AndOrGraphSearch[TaskRunRule, TaskTryRules, Solution], sol: Solution, timeoutMs: Long): (Solution, Boolean) = {
    import verification.AnalysisPhase._
    import verification.VerificationContext

    val ssol = sol.toSimplifiedExpr(context, program)
    reporter.info("Solution requires validation")

    val (npr, fds) = solutionToProgram(sol)

    val solverf = SolverFactory(() => (new FairZ3Solver(context, npr) with TimeoutSolver).setTimeout(timeoutMs))

    val vctx = VerificationContext(context, npr, solverf, context.reporter)
    val vcs = generateVerificationConditions(vctx, Some(fds.map(_.id.name).toSeq))
    val vcreport = checkVerificationConditions(vctx, vcs)

    if (vcreport.totalValid == vcreport.totalConditions) {
      (sol, true)
    } else if (vcreport.totalValid + vcreport.totalUnknown == vcreport.totalConditions) {
      reporter.warning("Solution may be invalid:")
      (sol, false)
    } else {
      reporter.warning("Solution was invalid:")
      reporter.warning(fds.map(ScalaPrinter(_)).mkString("\n\n"))
      reporter.warning(vcreport.summaryString)
      (new AndOrGraphPartialSolution(search.g, (task: TaskRunRule) => Solution.choose(task.problem), false).getSolution, false)
    }
  }

  // Returns the new program and the new functions generated for this
  def solutionToProgram(sol: Solution): (Program, Set[FunDef]) = {
    import purescala.TypeTrees.TupleType
    import purescala.Definitions.ValDef

    // Create new fundef for the body
    val ret = TupleType(problem.xs.map(_.getType))
    val res = Variable(FreshIdentifier("res").setType(ret))

    val mapPost: Map[Expr, Expr] =
      problem.xs.zipWithIndex.map{ case (id, i)  =>
        Variable(id) -> TupleSelect(res, i+1)
      }.toMap

    val fd = new FunDef(FreshIdentifier("finalTerm", true), Nil, ret, problem.as.map(id => ValDef(id, id.getType)), DefType.MethodDef)
    fd.precondition  = Some(And(problem.pc, sol.pre))
    fd.postcondition = Some((res.id, replace(mapPost, problem.phi)))
    fd.body          = Some(sol.term)

    val newDefs = sol.defs + fd

    val npr = program.copy(units = program.units map { u =>
      u.copy(modules = ModuleDef(FreshIdentifier("synthesis"), newDefs.toSeq) +: u.modules )
    })

    (npr, newDefs)
  }
}
