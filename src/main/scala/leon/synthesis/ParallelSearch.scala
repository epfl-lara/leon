package leon
package synthesis

import synthesis.search._
import akka.actor._
import solvers.z3.FairZ3Solver
import solvers.TrivialSolver

class ParallelSearch(synth: Synthesizer,
                     problem: Problem,
                     rules: Set[Rule],
                     costModel: CostModel) extends AndOrGraphParallelSearch[SynthesisContext, TaskRunRule, TaskTryRules, Solution](new AndOrGraph(TaskTryRules(problem), SearchCostModel(costModel))) {

  import synth.reporter._

  def initWorkerContext(wr: ActorRef) = {
    val reporter = new SilentReporter
    val solver = new FairZ3Solver(synth.context.copy(reporter = reporter))
    solver.setProgram(synth.program)

    solver.initZ3

    SynthesisContext(solver = solver, reporter = synth.reporter)
  }

  def expandAndTask(ref: ActorRef, sctx: SynthesisContext)(t: TaskRunRule) = {
    val prefix = "[%-20s] ".format(Option(t.rule).getOrElse("?"))

    t.app.apply(sctx) match {
      case RuleSuccess(sol) =>
        info(prefix+"Got: "+t.problem)
        info(prefix+"Solved with: "+sol)

        ExpandSuccess(sol)
      case RuleDecomposed(sub, onSuccess) =>
        info(prefix+"Got: "+t.problem)
        info(prefix+"Decomposed into:")
        for(p <- sub) {
          info(prefix+" - "+p)
        }

        Expanded(sub.map(TaskTryRules(_)))

      case RuleApplicationImpossible =>
        ExpandFailure()
    }
  }

  def expandOrTask(ref: ActorRef, sctx: SynthesisContext)(t: TaskTryRules) = {
    val sub = rules.flatMap { r => 
      r.attemptToApplyOn(sctx, t.p).alternatives.map(TaskRunRule(t.p, r, _))
    }

    if (!sub.isEmpty) {
      Expanded(sub.toList)
    } else {
      ExpandFailure()
    }
  }
}
