/* Copyright 2009-2013 EPFL, Lausanne */

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
          Some(Solution(s.pre, s.defs, LetTuple(sub.xs, s.term, Tuple(p.xs.map(id => if (unconstr(id)) simplestValue(Variable(id)) else Variable(id))))))
        case _ =>
          None
      }

      List(RuleInstantiation.immediateDecomp(p, this, List(sub), onSuccess, this.name))
    } else {
      Nil
    }
  }
}

