/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package rules

case object AsChoose extends Rule("As Choose") {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
      Some(new RuleInstantiation(p, this, SolutionBuilder.none, this.name) {
        def apply(sctx: SynthesisContext) = {
          RuleSuccess(Solution.choose(p))
        }
      })
  }
}

