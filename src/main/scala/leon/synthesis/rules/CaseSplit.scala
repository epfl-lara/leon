/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.Constructors._

case object CaseSplit extends Rule("Case-Split") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    p.phi match {
      case Or(os) =>
        List(split(os, "Split top-level Or"))
      case _ =>
        Nil
    }
  }

  def split(alts: Seq[Expr], description: String)(implicit p: Problem): RuleInstantiation = {
    val subs = alts.map(a => Problem(p.as, p.ws, p.pc, a, p.xs, p.eb)).toList

    val onSuccess: List[Solution] => Option[Solution] = {
      case sols if sols.size == subs.size =>
        val pre = orJoin(sols.map(_.pre))
        val defs = sols.map(_.defs).reduceLeft(_ ++ _)

        val (prefix, last) = (sols.init, sols.last)

        val term = prefix.foldRight(last.term) { (s, t) => IfExpr(s.pre, s.term, t) }

        Some(Solution(pre, defs, term, sols.forall(_.isTrusted)))

      case _ =>
        None
    }

    decomp(subs, onSuccess, description)
  }
}

