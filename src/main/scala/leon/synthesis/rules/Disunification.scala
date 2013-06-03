/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._

object Disunification {
  case object Decomp extends Rule("Disunif. Decomp.") {
    def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
      val TopLevelAnds(exprs) = p.phi

      val (toRemove, toAdd) = exprs.collect {
        case neq @ Not(Equals(cc1 @ CaseClass(cd1, args1), cc2 @ CaseClass(cd2, args2))) =>
          if (cc1 == cc2) {
            (neq, List(BooleanLiteral(false)))
          } else if (cd1 == cd2) {
            (neq, (args1 zip args2).map(p => Not(Equals(p._1, p._2))))
          } else {
            (neq, List(BooleanLiteral(true)))
          }
      }.unzip

      if (!toRemove.isEmpty) {
        val sub = p.copy(phi = Or((exprs.toSet -- toRemove ++ toAdd.flatten).toSeq))

        List(RuleInstantiation.immediateDecomp(p, this, List(sub), forward, this.name))
      } else {
        Nil
      }
    }
  }
}

