/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.Extractors._
import purescala.Constructors._

object Disunification {
  case object Decomp extends Rule("Disunif. Decomp.") {
    def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
      val TopLevelAnds(exprs) = p.phi

      val (toRemove, toAdd) = exprs.collect {
        case neq @ Not(Equals(cc1 @ CaseClass(cd1, args1), cc2 @ CaseClass(cd2, args2))) =>
          if (cc1 == cc2) {
            (neq, List(BooleanLiteral(false)))
          } else if (cd1 == cd2) {
            (neq, (args1 zip args2).map(p => not(Equals(p._1, p._2))))
          } else {
            (neq, List(BooleanLiteral(true)))
          }
      }.unzip

      if (toRemove.nonEmpty) {
        val sub = p.copy(phi = orJoin((exprs.toSet -- toRemove ++ toAdd.flatten).toSeq), eb = ExamplesBank.empty)

        Some(decomp(List(sub), forward, this.name))
      } else {
        None
      }
    }
  }
}

