package leon
package synthesis
package rules

import purescala.Trees._
import purescala.Common._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._

class EqualitySplit(synth: Synthesizer) extends Rule("Eq. Split.", synth, 90) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    val TopLevelAnds(presSeq) = p.c
    val pres = presSeq.toSet

    def combinations(a1: Identifier, a2: Identifier): Set[Expr] = {
      val v1 = Variable(a1)
      val v2 = Variable(a2)
      Set(
        Equals(v1, v2),
        Equals(v2, v1),
        Not(Equals(v1, v2)),
        Not(Equals(v2, v1))
      )
    }

    val candidate = p.as.groupBy(_.getType).map(_._2.toList).find {
      case List(a1, a2) => (pres & combinations(a1, a2)).isEmpty
      case _ => false
    }


    candidate match {
      case Some(List(a1, a2)) =>

        val sub1 = p.copy(c = And(Equals(Variable(a1), Variable(a2)), p.c))
        val sub2 = p.copy(c = And(Not(Equals(Variable(a1), Variable(a2))), p.c))

        val onSuccess: List[Solution] => Solution = { 
          case List(s1, s2) =>
            Solution(Or(s1.pre, s2.pre), s1.defs++s2.defs, IfExpr(Equals(Variable(a1), Variable(a2)), s1.term, s2.term))
          case _ =>
            Solution.none
        }

        RuleStep(List(sub1, sub2), onSuccess)
      case _ =>
        RuleInapplicable
    }
  }
}
