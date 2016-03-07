/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Expressions._
import purescala.ExprOps._
import purescala.Constructors._
import purescala.TypeOps._

case object UnconstrainedOutput extends NormalizingRule("Unconstr.Output") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val unconstr = (p.xs.toSet -- variablesOf(p.phi)).filter { x =>
      isRealExpr(simplestValue(x.getType))
    }

    if (unconstr.nonEmpty) {
      val sub = p.copy(xs = p.xs.filterNot(unconstr), eb = p.qeb.removeOuts(unconstr))

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

