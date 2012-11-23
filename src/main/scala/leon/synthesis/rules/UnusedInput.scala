package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._

case object UnusedInput extends Rule("UnusedInput", 100) {
  def attemptToApplyOn(sctx: SynthesisContext, p: Problem): RuleResult = {
    val unused = p.as.toSet -- variablesOf(p.phi) -- variablesOf(p.pc)

    if (!unused.isEmpty) {
      val sub = p.copy(as = p.as.filterNot(unused))

      RuleFastStep(List(sub), forward)
    } else {
      RuleInapplicable
    }
  }
}
