/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.ExprOps._
import purescala.Extractors._
import purescala.Constructors._

case object Assert extends NormalizingRule("Assert") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    p.phi match {
      case TopLevelAnds(exprs) =>
        val xsSet = p.xs.toSet
        val (exprsA, others) = exprs.partition(e => (variablesOf(e) & xsSet).isEmpty)

        if (exprsA.nonEmpty) {
          if (others.isEmpty) {
            Some(solve(Solution(andJoin(exprsA), Set(), tupleWrap(p.xs.map(id => simplestValue(id.getType))))))
          } else {
            val sub = p.copy(pc = andJoin(p.pc +: exprsA), phi = andJoin(others))

            Some(decomp(List(sub), {
              case (s @ Solution(pre, defs, term)) :: Nil => Some(Solution(andJoin(exprsA :+ pre), defs, term, s.isTrusted))
              case _ => None
            }, "Assert "+andJoin(exprsA)))
          }
        } else {
          None
        }
      case _ =>
        None
    }
  }
}

