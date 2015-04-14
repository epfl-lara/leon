/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

case object AsChoose extends Rule("As Choose") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    Some(solve(Solution.choose(p)))
  }
}

