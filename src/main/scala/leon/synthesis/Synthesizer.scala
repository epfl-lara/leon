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

class Synthesizer(val context : LeonContext,
                  val solver: Solver,
                  val program: Program,
                  val problem: Problem,
                  val rules: Set[Rule],
                  generateDerivationTrees: Boolean = false,
                  filterFuns: Option[Set[String]]  = None,
                  parallel: Boolean                = false,
                  firstOnly: Boolean               = false,
                  timeoutMs: Option[Long]          = None) {
  protected[synthesis] val reporter = context.reporter

  import reporter.{error,warning,info,fatalError}

  var continue = true

  def synthesize(): Solution = {

    val search = if (parallel) {
      new ParallelSearch(this, problem, rules)
    } else {
      new SimpleSearch(this, problem, rules)
    }

    val sigINT = new Signal("INT")
    var oldHandler: SignalHandler = null
    oldHandler = Signal.handle(sigINT, new SignalHandler {
      def handle(sig: Signal) {
        println
        reporter.info("Aborting...")

        continue = false
        search.stop()

        Signal.handle(sigINT, oldHandler)
      }
    })

    val ts = System.currentTimeMillis()

    val res = search.search()

    val diff = System.currentTimeMillis()-ts
    reporter.info("Finished in "+diff+"ms")

    if (generateDerivationTrees) {
      new AndOrGraphDotConverter(search.g, firstOnly).writeFile("derivation"+AndOrGraphDotConverterCounter.next()+".dot")
    }

    res match {
      case Some(solution) =>
        solution
      case None =>
        new AndOrGraphPartialSolution(search.g, (task: TaskRunRule) => Solution.choose(task.problem)).getSolution
    }
  }

}


