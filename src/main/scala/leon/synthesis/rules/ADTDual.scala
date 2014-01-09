/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._

case object ADTDual extends NormalizingRule("ADTDual") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    val xs = p.xs.toSet
    val as = p.as.toSet

    val TopLevelAnds(exprs) = p.phi


    val (toRemove, toAdd) = exprs.collect {
      case eq @ Equals(cc @ CaseClass(cct, args), e) if (variablesOf(e) -- as).isEmpty && !(variablesOf(cc) & xs).isEmpty =>
        (eq, CaseClassInstanceOf(cct, e) +: (cct.fieldsIds zip args).map{ case (id, ex) => Equals(ex, CaseClassSelector(cct, e, id)) } )

      case eq @ Equals(e, cc @ CaseClass(cct, args)) if (variablesOf(e) -- as).isEmpty && !(variablesOf(cc) & xs).isEmpty =>
        (eq, CaseClassInstanceOf(cct, e) +: (cct.fieldsIds zip args).map{ case (id, ex) => Equals(ex, CaseClassSelector(cct, e, id)) } )
    }.unzip

    if (!toRemove.isEmpty) {
      val sub = p.copy(phi = And((exprs.toSet -- toRemove ++ toAdd.flatten).toSeq))

      List(RuleInstantiation.immediateDecomp(p, this, List(sub), forward, "ADTDual"))
    } else {
      Nil
    }
  }
}

