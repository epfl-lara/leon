package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._

case object Assert extends Rule("Assert", 200) {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    p.phi match {
      case TopLevelAnds(exprs) =>
        val xsSet = p.xs.toSet

        val (exprsA, others) = exprs.partition(e => (variablesOf(e) & xsSet).isEmpty)

        if (!exprsA.isEmpty) {
          if (others.isEmpty) {
            List(RuleInstantiation.immediateSuccess(Solution(And(exprsA), Set(), Tuple(p.xs.map(id => simplestValue(Variable(id)))))))
          } else {
            val sub = p.copy(pc = And(p.pc +: exprsA), phi = And(others))

            List(RuleInstantiation.immediateDecomp(List(sub), {
              case Solution(pre, defs, term) :: Nil => Solution(And(exprsA :+ pre), defs, term)
              case _ => Solution.none
            }))
          }
        } else {
          Nil
        }
      case _ =>
        Nil
    }
  }
}

