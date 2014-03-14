/* Copyright 2009-2014 EPFL, Lausanne */

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
      case eq @ Equals(cc @ CaseClass(ct, args), e) if (variablesOf(e) -- as).isEmpty && !(variablesOf(cc) & xs).isEmpty =>
        (eq, CaseClassInstanceOf(ct, e) +: (ct.fields zip args).map{ case (vd, ex) => Equals(ex, CaseClassSelector(ct, e, vd.id)) } )

      case eq @ Equals(e, cc @ CaseClass(ct, args)) if (variablesOf(e) -- as).isEmpty && !(variablesOf(cc) & xs).isEmpty =>
        (eq, CaseClassInstanceOf(ct, e) +: (ct.fields zip args).map{ case (vd, ex) => Equals(ex, CaseClassSelector(ct, e, vd.id)) } )
    }.unzip

    if (!toRemove.isEmpty) {
      val sub = p.copy(phi = And((exprs.toSet -- toRemove ++ toAdd.flatten).toSeq))

      List(RuleInstantiation.immediateDecomp(p, this, List(sub), forward, "ADTDual"))
    } else {
      Nil
    }
  }
}

