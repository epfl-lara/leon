package leon
package synthesis

import purescala.Trees._

import heuristics._

object Heuristics {
  def all = Set[Synthesizer => Rule](
    new IntInduction(_)
    //new OptimisticInjection(_),
    //new SelectiveInlining(_),
//    new ADTInduction(_)
  )
}

trait Heuristic {
  this: Rule =>

  override def toString = "H: "+name

}

object HeuristicStep {
  def verifyPre(synth: Synthesizer, problem: Problem)(s: Solution): (Solution, Boolean) = {
    synth.solver.solveSAT(And(Not(s.pre), problem.phi)) match {
      case (Some(true), model) =>
        synth.reporter.warning("Heuristic failed to produce weakest precondition:")
        synth.reporter.warning(" - problem: "+problem)
        synth.reporter.warning(" - precondition: "+s.pre)
        (s, false)
      case _ =>
        (s, true)
    }
  }

  def apply(synth: Synthesizer, problem: Problem, subProblems: List[Problem], onSuccess: List[Solution] => Solution) = {
    RuleMultiSteps(subProblems, Nil, onSuccess.andThen(verifyPre(synth, problem)))
  }
}


object HeuristicOneStep {
  def apply(synth: Synthesizer, problem: Problem, subProblems: List[Problem], onSuccess: List[Solution] => Solution) = {
    RuleAlternatives(Set(HeuristicStep(synth, problem, subProblems, onSuccess)))
  }
}

