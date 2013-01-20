package leon
package synthesis

import purescala.Common._
import purescala.Definitions.{Program, FunDef}
import purescala.TreeOps._
import purescala.Trees.{Expr, Not}
import purescala.ScalaPrinter
import sun.misc.{Signal, SignalHandler}

import solvers.Solver
import java.io.File

import collection.mutable.PriorityQueue

import synthesis.search._

import java.util.concurrent.atomic.AtomicBoolean

class Synthesizer(val context : LeonContext,
                  val functionContext: Option[FunDef],
                  val solver: Solver,
                  val program: Program,
                  val problem: Problem,
                  val rules: Seq[Rule],
                  val options: SynthesizerOptions) {

  protected[synthesis] val reporter = context.reporter

  import reporter.{error,warning,info,fatalError}

  var shouldStop = new AtomicBoolean(false)

  def synthesize(): (Solution, Boolean) = {

  val search = if (options.searchWorkers > 1) {
      new ParallelSearch(this, problem, rules, options.costModel, options.searchWorkers)
    } else {
      new SimpleSearch(this, problem, rules, options.costModel)
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
      case Some(solution) =>
        (solution, true)
      case None =>
        (new AndOrGraphPartialSolution(search.g, (task: TaskRunRule) => Solution.choose(task.problem)).getSolution, false)
    }
  }

}


