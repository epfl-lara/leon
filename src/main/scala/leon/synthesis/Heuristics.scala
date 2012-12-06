package leon
package synthesis

import purescala.Trees._

import heuristics._

object Heuristics {
  def all = Set[Rule](
    IntInduction,
    //new OptimisticInjection(_),
    //new SelectiveInlining(_),
    ADTInduction
  )
}

trait Heuristic {
  this: Rule =>

  override def toString = "H: "+name

}

object HeuristicStep {
  def verifyPre(sctx: SynthesisContext, problem: Problem)(s: Solution): Solution = {
    //sctx here is unsafe to use in parallel. onSuccess should take a sctx for
    //this to be possible

    //sctx.solver.solveSAT(And(Not(s.pre), problem.phi)) match {
    //  case (Some(true), model) =>
    //    sctx.reporter.warning("Heuristic failed to produce weakest precondition:")
    //    sctx.reporter.warning(" - problem: "+problem)
    //    sctx.reporter.warning(" - precondition: "+s.pre)
    //    s
    //  case _ =>
    //    s
    //}
    s
  }

  def apply(sctx: SynthesisContext, problem: Problem, subProblems: List[Problem], onSuccess: List[Solution] => Solution) = {
    new RuleApplication(subProblems.size, onSuccess.andThen(verifyPre(sctx, problem))) {
      def apply(sctx: SynthesisContext) = RuleDecomposed(subProblems, onSuccess)
    }
  }
}


object HeuristicFastStep {
  def apply(sctx: SynthesisContext, problem: Problem, subProblems: List[Problem], onSuccess: List[Solution] => Solution) = {
    RuleResult(List(HeuristicStep(sctx, problem, subProblems, onSuccess)))
  }
}

