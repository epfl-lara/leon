package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._

object Unification {
  class DecompTrivialClash(synth: Synthesizer) extends Rule("Unif Dec./Clash/Triv.", synth, 200) {
    def applyOn(task: Task): RuleResult = {
      val p = task.problem

      val TopLevelAnds(exprs) = p.phi

      val (toRemove, toAdd) = exprs.collect {
        case eq @ Equals(cc1 @ CaseClass(cd1, args1), cc2 @ CaseClass(cd2, args2)) =>
          if (cc1 == cc2) {
            (eq, List(BooleanLiteral(true)))
          } else if (cd1 == cd2) {
            (eq, (args1 zip args2).map((Equals(_, _)).tupled))
          } else {
            (eq, List(BooleanLiteral(false)))
          }
      }.unzip

      if (!toRemove.isEmpty) {
        val sub = p.copy(phi = And((exprs.toSet -- toRemove ++ toAdd.flatten).toSeq))


        RuleStep(List(sub), forward)
      } else {
        RuleInapplicable
      }
    }
  }

  class OccursCheck(synth: Synthesizer) extends Rule("Unif OccursCheck", synth, 200) {
    def applyOn(task: Task): RuleResult = {
      val p = task.problem

      val TopLevelAnds(exprs) = p.phi

      val isImpossible = exprs.exists {
        case eq @ Equals(cc : CaseClass, Variable(id)) if variablesOf(cc) contains id =>
          true
        case eq @ Equals(Variable(id), cc : CaseClass) if variablesOf(cc) contains id =>
          true
        case _ =>
          false
      }

      if (isImpossible) {
        val tpe = TupleType(p.xs.map(_.getType))

        RuleSuccess(Solution(BooleanLiteral(false), Set(), Error(p.phi+" is UNSAT!").setType(tpe)))
      } else {
        RuleInapplicable
      }
    }
  }
}

