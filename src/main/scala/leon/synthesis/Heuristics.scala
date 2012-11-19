package leon
package synthesis

import purescala.Trees._

import heuristics._

object Heuristics {
  def all = Set[Synthesizer => Rule](
    new IntInduction(_),
    //new OptimisticInjection(_),
    //new SelectiveInlining(_),
    new ADTInduction(_)
  )
}

trait Heuristic {
  this: Rule =>

  override def toString = "H: "+name

}

object HeuristicStep {
  def verifyPre(synth: Synthesizer, problem: Problem)(s: Solution): Solution = {
    synth.solver.solveSAT(And(Not(s.pre), problem.phi)) match {
      case (Some(true), model) =>
        synth.reporter.warning("Heuristic failed to produce weakest precondition:")
        synth.reporter.warning(" - problem: "+problem)
        synth.reporter.warning(" - precondition: "+s.pre)
        s
      case _ =>
        s
    }
  }

  def apply(synth: Synthesizer, problem: Problem, subProblems: List[Problem], onSuccess: List[Solution] => Solution) = {
    new RuleApplication(subProblems.size, onSuccess.andThen(verifyPre(synth, problem))) {
      def apply() = RuleDecomposed(subProblems, onSuccess)
    }
  }
}


object HeuristicFastStep {
  def apply(synth: Synthesizer, problem: Problem, subProblems: List[Problem], onSuccess: List[Solution] => Solution) = {
    RuleResult(List(HeuristicStep(synth, problem, subProblems, onSuccess)))
  }
}

