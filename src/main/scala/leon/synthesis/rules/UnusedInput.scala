package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._

class UnusedInput(synth: Synthesizer) extends Rule("UnusedInput", synth, 100) {
  def attemptToApplyOn(p: Problem): RuleResult = {
    val unused = p.as.toSet -- variablesOf(p.phi) -- variablesOf(p.c)

    if (!unused.isEmpty) {
      val sub = p.copy(as = p.as.filterNot(unused))

      RuleFastStep(List(sub), forward)
    } else {
      RuleInapplicable
    }
  }
}
