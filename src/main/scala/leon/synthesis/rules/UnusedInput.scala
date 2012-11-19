package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._

class UnusedInput(synth: Synthesizer) extends Rule("UnusedInput", synth, 100) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem
    val unused = p.as.toSet -- variablesOf(p.phi) -- variablesOf(p.c)

    if (!unused.isEmpty) {
      val sub = p.copy(as = p.as.filterNot(unused))

      RuleOneStep(List(sub), forward)
    } else {
      RuleInapplicable
    }
  }
}
