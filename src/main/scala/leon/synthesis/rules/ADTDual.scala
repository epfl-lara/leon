/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Constructors._

case object ADTDual extends NormalizingRule("ADTDual") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val xs = p.xs.toSet
    val as = p.as.toSet

    val TopLevelAnds(exprs) = p.phi


    val (toRemove, toAdd) = exprs.collect {
      case eq @ Equals(cc @ CaseClass(ct, args), e) if (variablesOf(e) -- as).isEmpty && (variablesOf(cc) & xs).nonEmpty =>
        (eq, CaseClassInstanceOf(ct, e) +: (ct.fields zip args).map{ case (vd, ex) => Equals(ex, CaseClassSelector(ct, e, vd.id)) } )

      case eq @ Equals(e, cc @ CaseClass(ct, args)) if (variablesOf(e) -- as).isEmpty && (variablesOf(cc) & xs).nonEmpty =>
        (eq, CaseClassInstanceOf(ct, e) +: (ct.fields zip args).map{ case (vd, ex) => Equals(ex, CaseClassSelector(ct, e, vd.id)) } )
    }.unzip

    if (toRemove.nonEmpty) {
      val sub = p.copy(phi = andJoin((exprs.toSet -- toRemove ++ toAdd.flatten).toSeq))

      Some(decomp(List(sub), forward, "ADTDual"))
    } else {
      None
    }
  }
}

