package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._

class Assert(synth: Synthesizer) extends Rule("Assert", synth, 200) {
  def attemptToApplyOn(p: Problem): RuleResult = {
    p.phi match {
      case TopLevelAnds(exprs) =>
        val xsSet = p.xs.toSet

        val (exprsA, others) = exprs.partition(e => (variablesOf(e) & xsSet).isEmpty)

        if (!exprsA.isEmpty) {
          if (others.isEmpty) {
            RuleFastSuccess(Solution(And(exprsA), Set(), Tuple(p.xs.map(id => simplestValue(Variable(id))))))
          } else {
            val sub = p.copy(c = And(p.c +: exprsA), phi = And(others))

            RuleFastStep(List(sub), forward)
          }
        } else {
          RuleInapplicable
        }
      case _ =>
        RuleInapplicable
    }
  }
}

