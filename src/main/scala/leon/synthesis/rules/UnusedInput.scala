/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.ExprOps._
import purescala.TypeOps._

case object UnusedInput extends NormalizingRule("UnusedInput") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val unused = (p.as.toSet -- variablesOf(p.phi) -- p.pc.variables -- variablesOf(p.ws)).filter { a =>
      !isParametricType(a.getType)
    }

    if (unused.nonEmpty) {
      val sub = p.copy(as = p.as.filterNot(unused), eb = p.qeb.removeIns(unused))

      List(decomp(List(sub), forward, s"Unused inputs ${p.as.filter(unused).mkString(", ")}"))
    } else {
      Nil
    }
  }
}
