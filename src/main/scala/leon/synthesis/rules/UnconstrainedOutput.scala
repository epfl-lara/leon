package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._

class UnconstrainedOutput(synth: Synthesizer) extends Rule("Unconstr.Output", synth, 100) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem
    val unconstr = p.xs.toSet -- variablesOf(p.phi)

    if (!unconstr.isEmpty) {
      val sub = p.copy(xs = p.xs.filterNot(unconstr))

      val onSuccess: List[Solution] => Solution = { 
        case List(s) =>
          Solution(s.pre, s.defs, LetTuple(sub.xs, s.term, Tuple(p.xs.map(id => if (unconstr(id)) simplestValue(Variable(id)) else Variable(id)))))
        case _ =>
          Solution.none
      }

      RuleOneStep(List(sub), onSuccess)
    } else {
      RuleInapplicable
    }

  }
}

