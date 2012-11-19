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

    val candidate = p.as.groupBy(_.getType).map(_._2.toList).find {
      case List(a1, a2) =>
        val toValEQ = Implies(p.c, Equals(Variable(a1), Variable(a2)))

        val impliesEQ = synth.solver.solveSAT(Not(toValEQ)) match {
          case (Some(false), _) => true
          case _ => false
        }

        if (!impliesEQ) {
          val toValNE = Implies(p.c, Not(Equals(Variable(a1), Variable(a2))))

          val impliesNE = synth.solver.solveSAT(Not(toValNE)) match {
            case (Some(false), _) => true
            case _ => false
          }

          !impliesNE
        } else {
          false
        }
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

        RuleOneStep(List(sub1, sub2), onSuccess)
      case _ =>
        RuleInapplicable
    }
  }
}
