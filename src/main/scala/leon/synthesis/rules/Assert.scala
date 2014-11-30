/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.Constructors._

case object Assert extends NormalizingRule("Assert") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    p.phi match {
      case TopLevelAnds(exprs) =>
        val xsSet = p.xs.toSet

        val (exprsA, others) = exprs.partition(e => (variablesOf(e) & xsSet).isEmpty)

        if (!exprsA.isEmpty) {
          if (others.isEmpty) {
            List(RuleInstantiation.immediateSuccess(p, this, Solution(andJoin(exprsA), Set(), Tuple(p.xs.map(id => simplestValue(id.getType))))))
          } else {
            val sub = p.copy(pc = andJoin(p.pc +: exprsA), phi = andJoin(others))

            List(RuleInstantiation.immediateDecomp(p, this, List(sub), {
              case Solution(pre, defs, term) :: Nil => Some(Solution(andJoin(exprsA :+ pre), defs, term))
              case _ => None
            }, "Assert "+andJoin(exprsA)))
          }
        } else {
          Nil
        }
      case _ =>
        Nil
    }
  }
}

