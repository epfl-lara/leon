package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._

case object UnusedInput extends Rule("UnusedInput") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    val unused = p.as.toSet -- variablesOf(p.phi) -- variablesOf(p.pc)

    if (!unused.isEmpty) {
      val sub = p.copy(as = p.as.filterNot(unused))

      List(RuleInstantiation.immediateDecomp(p, this, List(sub), forward))
    } else {
      Nil
    }
  }
}
