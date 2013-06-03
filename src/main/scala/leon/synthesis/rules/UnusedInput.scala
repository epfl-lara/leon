/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._

case object UnusedInput extends NormalizingRule("UnusedInput") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    val unused = p.as.toSet -- variablesOf(p.phi) -- variablesOf(p.pc)

    if (!unused.isEmpty) {
      val sub = p.copy(as = p.as.filterNot(unused))

      List(RuleInstantiation.immediateDecomp(p, this, List(sub), forward, this.name))
    } else {
      Nil
    }
  }
}
