/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._

case object Assert extends NormalizingRule("Assert") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    p.phi match {
      case TopLevelAnds(exprs) =>
        val xsSet = p.xs.toSet

        val (exprsA, others) = exprs.partition(e => (variablesOf(e) & xsSet).isEmpty)

        if (!exprsA.isEmpty) {
          if (others.isEmpty) {
            List(RuleInstantiation.immediateSuccess(p, this, Solution(And(exprsA), Set(), Tuple(p.xs.map(id => simplestValue(Variable(id)))))))
          } else {
            val sub = p.copy(pc = And(p.pc +: exprsA), phi = And(others))

            List(RuleInstantiation.immediateDecomp(p, this, List(sub), {
              case Solution(pre, defs, term) :: Nil => Some(Solution(And(exprsA :+ pre), defs, term))
              case _ => None
            }, "Assert "+And(exprsA)))
          }
        } else {
          Nil
        }
      case _ =>
        Nil
    }
  }
}

