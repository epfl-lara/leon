/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.ExprOps._

case object UnusedInput extends NormalizingRule("UnusedInput") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val unused = p.as.toSet -- variablesOf(p.phi) -- variablesOf(p.pc) -- variablesOf(p.ws)

    if (unused.nonEmpty) {
      val sub = p.copy(as = p.as.filterNot(unused))

      List(decomp(List(sub), forward, s"Unused inputs ${p.as.filter(unused).mkString(", ")}"))
    } else {
      Nil
    }
  }
}
