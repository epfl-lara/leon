/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._

case object UnconstrainedOutput extends NormalizingRule("Unconstr.Output") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    val unconstr = p.xs.toSet -- variablesOf(p.phi)

    if (!unconstr.isEmpty) {
      val sub = p.copy(xs = p.xs.filterNot(unconstr))

      val onSuccess: List[Solution] => Option[Solution] = { 
        case List(s) =>
          val term = if (sub.xs.size > 1) {
            LetTuple(sub.xs, s.term, Tuple(p.xs.map(id => if (unconstr(id)) simplestValue(id.getType) else Variable(id))))
          } else if (sub.xs.size == 1) {
            Let(sub.xs.head, s.term, Tuple(p.xs.map(id => if (unconstr(id)) simplestValue(id.getType) else Variable(id))))
          } else {
            Tuple(p.xs.map(id => simplestValue(id.getType)))
          }
          Some(Solution(s.pre, s.defs, term))
        case _ =>
          None
      }

      List(RuleInstantiation.immediateDecomp(p, this, List(sub), onSuccess, this.name))
    } else {
      Nil
    }
  }
}

