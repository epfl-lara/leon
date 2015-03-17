/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.Extractors._
import purescala.Constructors._

case object OptimisticInjection extends Rule("Opt. Injection") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val TopLevelAnds(exprs) = p.phi

    val eqfuncalls = exprs.collect{
      case eq @ Equals(FunctionInvocation(fd, args), e) =>
        ((fd, e), args, eq : Expr)
      case eq @ Equals(e, FunctionInvocation(fd, args)) =>
        ((fd, e), args, eq : Expr)
    }

    val candidates = eqfuncalls.groupBy(_._1).filter(_._2.size > 1)
    if (candidates.nonEmpty) {

      var newExprs = exprs
      for (cands <- candidates.values) {
        val cand = cands.take(2)
        val toRemove = cand.map(_._3).toSet
        val argss    = cand.map(_._2)
        val args     = argss(0) zip argss(1)

        newExprs ++= args.map{ case (l, r) => Equals(l, r) }
        newExprs = newExprs.filterNot(toRemove)
      }

      val sub = p.copy(phi = andJoin(newExprs))

      Some(decomp(List(sub), forward, s"Injection ${candidates.keySet.map(_._1.id).mkString(", ")}"))
    } else {
      None
    }
  }
}
