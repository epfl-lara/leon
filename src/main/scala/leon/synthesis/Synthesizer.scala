/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import purescala.Common._
import purescala.Definitions.{Program, FunDef, ModuleDef, DefType, ValDef}
import purescala.TreeOps._
import purescala.Trees._
import purescala.Constructors._
import purescala.ScalaPrinter
import purescala.TypeTrees._
import solvers._
import solvers.combinators._
import solvers.z3._

import java.io.File

import synthesis.graph._

class Synthesizer(val context : LeonContext,
                  val functionContext: FunDef,
                  val program: Program,
                  val problem: Problem,
                  val settings: SynthesisSettings) {

  val reporter = context.reporter

  def getSearch(): Search = {
    if (settings.manualSearch) {
      new ManualSearch(context, problem, settings.costModel)
    } else if (settings.searchWorkers > 1) {
      ???
      //new ParallelSearch(this, problem, options.searchWorkers)
    } else {
      new SimpleSearch(context, problem, settings.costModel, settings.searchBound)
    }
  }

  def synthesize(): (Search, Stream[Solution]) = {
    val s = getSearch();

    val sctx = SynthesisContext.fromSynthesizer(this)

    val t = context.timers.synthesis.search.start()

    val sols = s.search(sctx)

    val diff = t.stop()
    reporter.info("Finished in "+diff+"ms")

    (s, sols)
  }

  def validate(results: (Search, Stream[Solution])): (Search, Stream[(Solution, Boolean)]) = {
    val (s, sols) = results

    val result = sols.map {
      case sol if sol.isTrusted =>
        (sol, true)
      case sol =>
        validateSolution(s, sol, 5000L)
    }

    (s, if (result.isEmpty) {
      List((new PartialSolution(s.g, true).getSolution, false)).toStream
    } else {
      result
    })
  }

  def validateSolution(search: Search, sol: Solution, timeoutMs: Long): (Solution, Boolean) = {
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
      (new PartialSolution(search.g, false).getSolution, false)
    }
  }

  // Returns the new program and the new functions generated for this
  def solutionToProgram(sol: Solution): (Program, List[FunDef]) = {

    // Create new fundef for the body
    val ret = tupleTypeWrap(problem.xs.map(_.getType))
    val res = Variable(FreshIdentifier("res").setType(ret))

    val mapPost: Map[Expr, Expr] =
      if (problem.xs.size > 1) {
        problem.xs.zipWithIndex.map{ case (id, i)  =>
          Variable(id) -> tupleSelect(res, i+1)
        }.toMap
      } else {
        problem.xs.map{ case id  =>
          Variable(id) -> res
        }.toMap
      }

    val fd = new FunDef(FreshIdentifier(functionContext.id.name+"_final", true), Nil, ret, problem.as.map(id => ValDef(id, id.getType)), DefType.MethodDef)
    fd.precondition  = Some(and(problem.pc, sol.pre))
    fd.postcondition = Some((res.id, replace(mapPost, problem.phi)))
    fd.body          = Some(sol.term)

    val newDefs = fd +: sol.defs.toList

    val npr = program.copy(units = program.units map { u =>
      u.copy(modules = ModuleDef(FreshIdentifier("synthesis"), newDefs.toSeq, false) +: u.modules )
    })

    (npr, newDefs)
  }
}

