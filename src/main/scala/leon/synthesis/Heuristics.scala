/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis

import purescala.Trees._
import purescala.TypeTrees.TupleType

import heuristics._

object Heuristics {
  def all = List[Rule](
    IntInduction,
    InnerCaseSplit,
    //new OptimisticInjection(_),
    //new SelectiveInlining(_),
    ADTLongInduction,
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

  def apply(problem: Problem, rule: Rule, subProblems: List[Problem], onSuccess: List[Solution] => Option[Solution], description: String): RuleInstantiation = {
    val subTypes = subProblems.map(p => TupleType(p.xs.map(_.getType)))

    val builder = new SolutionBuilder(subProblems.size, subTypes) {
      def apply(sols: List[Solution]) = {
        onSuccess(sols)
      }
    }

    new RuleInstantiation(problem, rule, builder, description) {
      def apply(sctx: SynthesisContext) = RuleDecomposed(subProblems)

    }
  }
}
