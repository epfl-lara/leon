package leon
package synthesis
package heuristics

import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

class OptimisticInjection(synth: Synthesizer) extends Rule("Opt. Injection", synth, 50) with Heuristic {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    val TopLevelAnds(exprs) = p.phi

    val eqfuncalls = exprs.collect{
      case eq @ Equals(FunctionInvocation(fd, args), e) =>
        ((fd, e), args, eq : Expr)
      case eq @ Equals(e, FunctionInvocation(fd, args)) =>
        ((fd, e), args, eq : Expr)
    }

    val candidates = eqfuncalls.groupBy(_._1).filter(_._2.size > 1)
    if (!candidates.isEmpty) {

      var newExprs = exprs
      for (cands <- candidates.values) {
        val cand = cands.take(2)
        val toRemove = cand.map(_._3).toSet
        val argss    = cand.map(_._2)
        val args     = argss(0) zip argss(1)

        newExprs ++= args.map{ case (l, r) => Equals(l, r) }
        newExprs = newExprs.filterNot(toRemove)
      }

      val sub = p.copy(phi = And(newExprs))

      HeuristicOneStep(synth, p, List(sub), forward)
    } else {
      RuleInapplicable
    }
  }
}
