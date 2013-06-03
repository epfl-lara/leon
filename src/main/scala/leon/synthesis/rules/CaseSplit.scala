/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._

case object CaseSplit extends Rule("Case-Split") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    p.phi match {
      case Or(os) =>
        List(split(os, p, "Split top-level Or"))
      case _ =>
        Nil
    }
  }

  def split(alts: Seq[Expr], p: Problem, description: String): RuleInstantiation = {
    val subs = alts.map(a => Problem(p.as, p.pc, a, p.xs)).toList

    val onSuccess: List[Solution] => Option[Solution] = {
      case sols if sols.size == subs.size =>
        val pre = Or(sols.map(_.pre))
        val defs = sols.map(_.defs).reduceLeft(_ ++ _)

        val (prefix, last) = (sols.dropRight(1), sols.last)

        val term = prefix.foldRight(last.term) { (s, t) => IfExpr(s.pre, s.term, t) }

        Some(Solution(pre, defs, term))

      case _ =>
        None
    }

    RuleInstantiation.immediateDecomp(p, this, subs, onSuccess, description)
  }
}

