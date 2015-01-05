/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._

case object UnusedInput extends NormalizingRule("UnusedInput") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val unused = p.as.toSet -- variablesOf(p.phi) -- variablesOf(p.pc)

    if (!unused.isEmpty) {
      val sub = p.copy(as = p.as.filterNot(unused))

      List(decomp(List(sub), forward, s"Unused inputs ${p.as.filter(unused).mkString(", ")}"))
    } else {
      Nil
    }
  }
}
