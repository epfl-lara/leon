/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis

import purescala.Expressions.Choose
import purescala.Definitions._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.ScalaPrinter
import solvers._
import leon.utils._

import scala.concurrent.duration._

import synthesis.strategies._

class Synthesizer(val context : LeonContext,
                  val program: Program,
                  val ci: SourceInfo,
                  val settings: SynthesisSettings) {

  val problem = ci.problem

  val reporter = context.reporter

  lazy val sctx = new SynthesisContext(context, settings, ci.fd, program)

  implicit val debugSection = leon.utils.DebugSectionSynthesis

  def getSearch: Search = {
    val strat0 = new CostBasedStrategy(context, settings.costModel)

    val strat1 = if (settings.manualSearch.isDefined) {
      new ManualStrategy(context, settings.manualSearch, strat0)
    } else {
      strat0
    }

    val strat2 = settings.searchBound match {
      case Some(b) =>
        BoundedStrategy(strat1, b)
      case None =>
        strat1
    }

    new Search(context, ci, problem, strat2)
  }

  private var lastTime: Long = 0

  def synthesize(): (Search, Stream[Solution]) = {
    reporter.ifDebug { printer =>
      printer(problem.eb.asString("Tests available for synthesis")(context))
    }

    val s = getSearch

    reporter.info(ASCIIHelpers.title(s"Synthesizing '${ci.fd.id}'"))

    val t = context.timers.synthesis.search.start()

    val sols = s.search(sctx)

    val diff = t.stop()

    lastTime = diff

    reporter.info("Finished in "+diff+"ms")


    (s, sols)
  }

  def validate(results: (Search, Stream[Solution]), allowPartial: Boolean): (Search, Stream[(Solution, Boolean)]) = {
    val (s, sols) = results

    val result = sols.map {
      case sol if sol.isTrusted =>
        (sol, Some(true))
      case sol =>
        validateSolution(s, sol, 5.seconds)
    }

    // Print out report for synthesis, if necessary
    reporter.ifDebug { printer =>
      import java.text.SimpleDateFormat
      import java.util.Date

      val categoryName = ci.fd.getPos.file.toString.split("/").dropRight(1).lastOption.getOrElse("?")
      val benchName = categoryName+"."+ci.fd.id.name
      val time = lastTime/1000.0

      val defs = visibleDefsFrom(ci.fd)(program).collect {
        case cd: ClassDef => 1 + cd.fields.size
        case fd: FunDef => 1 + fd.params.size + formulaSize(fd.fullBody)
      }

      val psize = defs.sum

      val (size, calls, proof) = result.headOption match {
        case Some((sol, trusted)) =>
          val expr = sol.toSimplifiedExpr(context, program, ci.fd)
          val pr = trusted match {
            case Some(true) => "✓"
            case Some(false) => "✗"
            case None => "?"
          }
          (formulaSize(expr), functionCallsOf(expr).size, pr)
        case _ =>
          (0, 0, "F")
      }

      val date = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").format(new Date())

      val fw = new java.io.FileWriter("synthesis-report.txt", true)

      try {
        fw.write(f"$date:  $benchName%-50s | $psize%4d | $size%4d | $calls%4d | $proof%7s | $time%2.1f \n")
      } finally {
        fw.close
      }
    }(DebugSectionReport)

    (s, if (result.isEmpty && allowPartial) {
      Stream((new PartialSolution(s.strat, true).getSolutionFor(s.g.root), false))
    } else {
      // Discard invalid solutions
      result collect {
        case (sol, Some(true)) => (sol, true)
        case (sol, None)       => (sol, false)
      }
    })
  }

  def validateSolution(search: Search, sol: Solution, timeout: Duration): (Solution, Option[Boolean]) = {
    import verification.VerificationPhase._
    import verification.VerificationContext

    val timer = context.timers.synthesis.validation
    timer.start()

    reporter.info("Solution requires validation")

    val (npr, fds) = solutionToProgram(sol)

    val solverf = SolverFactory.getFromSettings(context, npr).withTimeout(timeout)

    try {
      val vctx = new VerificationContext(context, npr, solverf)
      val vcs = generateVCs(vctx, fds)
      val vcreport = checkVCs(vctx, vcs, stopWhen = _.isInvalid)

      if (vcreport.totalValid == vcreport.totalConditions) {
        (sol, Some(true))
      } else if (vcreport.totalValid + vcreport.totalUnknown == vcreport.totalConditions) {
        reporter.warning("Solution may be invalid:")
        (sol, None)
      } else {
        reporter.error("Solution was invalid:")
        reporter.error(fds.map(ScalaPrinter(_)).mkString("\n\n"))
        reporter.error(vcreport.summaryString)
        (new PartialSolution(search.strat, false).getSolutionFor(search.g.root), Some(false))
      }
    } finally {
      timer.stop()
      solverf.shutdown()
    }
  }

  // Returns the new program and the new functions generated for this
  def solutionToProgram(sol: Solution): (Program, List[FunDef]) = {
    // We replace the choose with the body of the synthesized solution

    val solutionExpr = sol.toSimplifiedExpr(context, program, ci.fd)

    val (npr, _, fdMap, _) = replaceFunDefs(program)({
      case fd if fd eq ci.fd =>
        val nfd = fd.duplicate()
        nfd.fullBody = replace(Map(ci.source -> solutionExpr), nfd.fullBody)
        (fd.body, fd.postcondition) match {
          case (Some(Choose(pred)), None) =>
            nfd.postcondition = Some(pred)
          case _ =>
        }
        Some(nfd)
      case _ => None
    })

    (npr, fdMap.get(ci.fd).toList)
  }

  def shutdown(): Unit = {
    sctx.solverFactory.shutdown()
  }
}

