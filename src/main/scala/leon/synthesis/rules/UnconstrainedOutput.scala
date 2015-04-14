/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.ExprOps._
import purescala.Constructors._

case object UnconstrainedOutput extends NormalizingRule("Unconstr.Output") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val unconstr = p.xs.toSet -- variablesOf(p.phi)

    if (unconstr.nonEmpty) {
      val sub = p.copy(xs = p.xs.filterNot(unconstr))

      val onSuccess: List[Solution] => Option[Solution] = { 
        case List(s) =>
          val term = letTuple(sub.xs, s.term, tupleWrap(p.xs.map(id => if (unconstr(id)) simplestValue(id.getType) else Variable(id))))

          Some(Solution(s.pre, s.defs, term, s.isTrusted))
        case _ =>
          None
      }

      Some(decomp(List(sub), onSuccess, s"Unconst. out ${p.xs.filter(unconstr).mkString(", ")}"))
    } else {
      None
    }
  }
}

