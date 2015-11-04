/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis

import purescala.Definitions._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.ScalaPrinter
import solvers._

import scala.concurrent.duration._

import synthesis.graph._

class Synthesizer(val context : LeonContext,
                  val program: Program,
                  val ci: SourceInfo,
                  val settings: SynthesisSettings) {

  val problem = ci.problem

  val reporter = context.reporter

  lazy val sctx = SynthesisContext.fromSynthesizer(this)

  implicit val debugSection = leon.utils.DebugSectionSynthesis

  def getSearch: Search = {
    if (settings.manualSearch.isDefined) {
      new ManualSearch(context, ci, problem, settings.costModel, settings.manualSearch)
    } else {
      new SimpleSearch(context, ci, problem, settings.costModel, settings.searchBound)
    }
  }

  def synthesize(): (Search, Stream[Solution]) = {

    reporter.ifDebug { printer => 
      printer(problem.eb.asString("Tests available for synthesis")(context))
    }

    val s = getSearch

    val t = context.timers.synthesis.search.start()

    val sols = s.search(sctx)

    val diff = t.stop()
    reporter.info("Finished in "+diff+"ms")

    (s, sols)
  }

  def validate(results: (Search, Stream[Solution]), allowPartial: Boolean): (Search, Stream[(Solution, Boolean)]) = {
    val (s, sols) = results

    val result = sols.map {
      case sol if sol.isTrusted =>
        (sol, true)
      case sol =>
        validateSolution(s, sol, 5.seconds)
    }

    (s, if (result.isEmpty && allowPartial) {
      List((new PartialSolution(s.g, true).getSolution, false)).toStream
    } else {
      result
    })
  }

  def validateSolution(search: Search, sol: Solution, timeout: Duration): (Solution, Boolean) = {
    import verification.VerificationPhase._
    import verification.VerificationContext

    reporter.info("Solution requires validation")

    val (npr, fds) = solutionToProgram(sol)

    val solverf = SolverFactory.default(context, npr).withTimeout(timeout)

    try {
      val vctx = VerificationContext(context, npr, solverf, context.reporter)
      val vcs = generateVCs(vctx, fds)
      val vcreport = checkVCs(vctx, vcs)

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
    } finally {
      solverf.shutdown()
    }
  }

  // Returns the new program and the new functions generated for this
  def solutionToProgram(sol: Solution): (Program, List[FunDef]) = {
    // We replace the choose with the body of the synthesized solution

    val solutionExpr = sol.toSimplifiedExpr(context, program)

    val (npr, fdMap) = replaceFunDefs(program)({
      case fd if fd eq ci.fd =>
        val nfd = fd.duplicate()
        nfd.fullBody = replace(Map(ci.source -> solutionExpr), nfd.fullBody)
        Some(nfd)
      case _ => None
    })

    (npr, fdMap.get(ci.fd).toList)
  }

  def shutdown(): Unit = {
    sctx.solverFactory.shutdown()
  }
}

