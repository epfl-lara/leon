package leon
package synthesis

import synthesis.search._
import akka.actor._
import solvers.z3.FairZ3Solver
import solvers.TrivialSolver

class ParallelSearch(synth: Synthesizer,
                     problem: Problem,
                     rules: Set[Rule]) extends AndOrGraphParallelSearch[SynthesisContext, TaskRunRule, TaskTryRules, Solution](new AndOrGraph(TaskTryRules(problem))) {

  import synth.reporter._

  def initWorkerContext(wr: ActorRef) = {
    val reporter = new SilentReporter
    val solver = new TrivialSolver(synth.reporter)
    solver.setProgram(synth.program)

    SynthesisContext(solver = solver, reporter = synth.reporter)
  }

  def expandAndTask(ref: ActorRef, sctx: SynthesisContext)(t: TaskRunRule) = {
    val prefix = "[%-20s] ".format(Option(t.rule).getOrElse("?"))

    t.app.apply() match {
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
    val sub = rules.flatMap ( r => r.attemptToApplyOn(sctx, t.p).alternatives.map(TaskRunRule(t.p, r, _)) )

    if (!sub.isEmpty) {
      Expanded(sub.toList)
    } else {
      ExpandFailure()
    }
  }
}
