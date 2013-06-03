/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._

object Unification {
  case object DecompTrivialClash extends NormalizingRule("Unif Dec./Clash/Triv.") {
    def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
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


        List(RuleInstantiation.immediateDecomp(p, this, List(sub), forward, this.name))
      } else {
        Nil
      }
    }
  }

  // This rule is probably useless; it never happens except in crafted
  // examples, and will be found by OptimisticGround anyway.
  case object OccursCheck extends NormalizingRule("Unif OccursCheck") {
    def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
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

        List(RuleInstantiation.immediateSuccess(p, this, Solution(BooleanLiteral(false), Set(), Error(p.phi+" is UNSAT!").setType(tpe))))
      } else {
        Nil
      }
    }
  }
}

