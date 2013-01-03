package leon
package synthesis

import synthesis.search._
import akka.actor._
import solvers.z3.FairZ3Solver
import solvers.TrivialSolver

class ParallelSearch(synth: Synthesizer,
                     problem: Problem,
                     rules: Set[Rule],
                     costModel: CostModel,
                     nWorkers: Int) extends AndOrGraphParallelSearch[SynthesisContext, TaskRunRule, TaskTryRules, Solution](new AndOrGraph(TaskTryRules(problem), SearchCostModel(costModel)), nWorkers) {

  import synth.reporter._

  // This is HOT shared memory, used only in stop() for shutting down solvers!
  private[this] var contexts = List[SynthesisContext]()

  def initWorkerContext(wr: ActorRef) = {
    val reporter = new SilentReporter
    val solver = new FairZ3Solver(synth.context.copy(reporter = reporter))
    solver.setProgram(synth.program)

    solver.initZ3

    val ctx = SynthesisContext(solver = solver, reporter = synth.reporter, shouldStop = synth.shouldStop)

    synchronized {
      contexts = ctx :: contexts
    }

    ctx
  }

  override def stop() = {
    synth.shouldStop.set(true)
    for (ctx <- contexts) {
      ctx.solver.halt()
    }
    super.stop()
  }

  def expandAndTask(ref: ActorRef, sctx: SynthesisContext)(t: TaskRunRule) = {
    val prefix = "[%-20s] ".format(Option(t.rule).getOrElse("?"))

    t.app.apply(sctx) match {
      case RuleSuccess(sol) =>
        synth.synchronized {
          info(prefix+"Got: "+t.problem)
          info(prefix+"Solved with: "+sol)
        }

        ExpandSuccess(sol)
      case RuleDecomposed(sub) =>
        synth.synchronized {
          info(prefix+"Got: "+t.problem)
          info(prefix+"Decomposed into:")
          for(p <- sub) {
            info(prefix+" - "+p)
          }
        }

        Expanded(sub.map(TaskTryRules(_)))

      case RuleApplicationImpossible =>
        ExpandFailure()
    }
  }

  def expandOrTask(ref: ActorRef, sctx: SynthesisContext)(t: TaskTryRules) = {
    val sub = rules.flatMap { r => 
      r.instantiateOn(sctx, t.p).map(TaskRunRule(_))
    }

    if (!sub.isEmpty) {
      Expanded(sub.toList)
    } else {
      ExpandFailure()
    }
  }
}
