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

object HeuristicInstantiation {
  def verifyPre(sctx: SynthesisContext, problem: Problem)(s: Solution): Option[Solution] = {
    //sctx.solver.solveSAT(And(Not(s.pre), problem.phi)) match {
    //  case (Some(true), model) =>
    //    sctx.reporter.warning("Heuristic failed to produce weakest precondition:")
    //    sctx.reporter.warning(" - problem: "+problem)
    //    sctx.reporter.warning(" - precondition: "+s.pre)
    //    None
    //  case _ =>
    //    Some(s)
    //}

    Some(s)
  }

  def apply(problem: Problem, subProblems: List[Problem], onSuccess: List[Solution] => Solution) = {
    val builder = new SolutionBuilder(subProblems.size) {
      def apply(sols: List[Solution]) = {
        Some(onSuccess(sols))
      }
    }

    new RuleInstantiation(builder) {
      def apply(sctx: SynthesisContext) = RuleDecomposed(subProblems)

    }
  }
}
