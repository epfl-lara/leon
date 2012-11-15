package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._

class CaseSplit(synth: Synthesizer) extends Rule("Case-Split", synth, 200) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem
    p.phi match {
      case Or(Seq(o1, o2)) =>
        val sub1 = Problem(p.as, p.c, o1, p.xs)
        val sub2 = Problem(p.as, p.c, o2, p.xs)

        val onSuccess: List[Solution] => Solution = { 
          case List(Solution(p1, d1, t1), Solution(p2, d2, t2)) => Solution(Or(p1, p2), d1++d2, IfExpr(p1, t1, t2))
          case _ => Solution.none
        }

        RuleStep(List(sub1, sub2), onSuccess)
      case _ =>
        RuleInapplicable
    }
  }
}

