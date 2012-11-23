package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._

case object CaseSplit extends Rule("Case-Split", 200) {
  def attemptToApplyOn(sctx: SynthesisContext, p: Problem): RuleResult = {
    p.phi match {
      case Or(o1 :: o2 :: _) =>
        val sub1 = Problem(p.as, p.pc, o1, p.xs)
        val sub2 = Problem(p.as, p.pc, o2, p.xs)

        val onSuccess: List[Solution] => Solution = { 
          case List(Solution(p1, d1, t1), Solution(p2, d2, t2)) => Solution(Or(p1, p2), d1++d2, IfExpr(p1, t1, t2))
          case _ => Solution.none
        }

        RuleFastStep(List(sub1, sub2), onSuccess)
      case _ =>
        RuleInapplicable
    }
  }
}

