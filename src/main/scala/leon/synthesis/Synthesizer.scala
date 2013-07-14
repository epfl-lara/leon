/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis

import purescala.Common._
import purescala.Definitions.{Program, FunDef}
import purescala.TreeOps._
import purescala.Trees._
import purescala.ScalaPrinter
import solvers.z3._
import solvers.TimeoutSolver
import sun.misc.{Signal, SignalHandler}

import solvers.Solver
import java.io.File

import collection.mutable.PriorityQueue

import synthesis.search._

import java.util.concurrent.atomic.AtomicBoolean

class Synthesizer(val context : LeonContext,
                  val functionContext: Option[FunDef],
                  val program: Program,
                  val problem: Problem,
                  val options: SynthesisOptions) {

  val silentReporter = new SilentReporter
  val silentContext = context.copy(reporter = silentReporter)

  val rules: Seq[Rule] = options.rules

  val solver: FairZ3Solver = new FairZ3Solver(silentContext)
  solver.setProgram(program)

  val simpleSolver: Solver = new UninterpretedZ3Solver(silentContext)
  simpleSolver.setProgram(program)

  val reporter = context.reporter

  var shouldStop = new AtomicBoolean(false)

  def synthesize(): (Solution, Boolean) = {

    val search = if (options.manualSearch) {
        new ManualSearch(this, problem)
      } else if (options.searchWorkers > 1) {
        new ParallelSearch(this, problem, options.searchWorkers)
      } else {
        new SimpleSearch(this, problem)
      }

    val sigINT = new Signal("INT")
    var oldHandler: SignalHandler = null
    oldHandler = Signal.handle(sigINT, new SignalHandler {
      def handle(sig: Signal) {
        println
        reporter.info("Aborting...")

        shouldStop.set(true)
        search.stop()

        Signal.handle(sigINT, oldHandler)
      }
    })

    val ts = System.currentTimeMillis()

    val res = search.search()

    val diff = System.currentTimeMillis()-ts
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

    val tsolver = new TimeoutSolver(new FairZ3Solver(silentContext), timeoutMs)
    tsolver.setProgram(npr)

    val vcs = generateVerificationConditions(reporter, npr, fds.map(_.id.name))
    val vctx = VerificationContext(context, Seq(tsolver), silentReporter)
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
    import purescala.Definitions.VarDecl

    val mainObject = program.mainObject

    // Create new fundef for the body
    val ret = TupleType(problem.xs.map(_.getType))
    val res = ResultVariable().setType(ret)

    val mapPost: Map[Expr, Expr] =
      problem.xs.zipWithIndex.map{ case (id, i)  =>
        Variable(id) -> TupleSelect(res, i+1)
      }.toMap

    val fd = new FunDef(FreshIdentifier("finalTerm", true), ret, problem.as.map(id => VarDecl(id, id.getType)))
    fd.precondition  = Some(And(problem.pc, sol.pre))
    fd.postcondition = Some(replace(mapPost, problem.phi))
    fd.body          = Some(sol.term)

    val newDefs = sol.defs + fd

    val npr = program.copy(mainObject = mainObject.copy(defs = mainObject.defs ++ newDefs))

    (npr, newDefs)
  }
}
