/* Copyright 2009-2016 EPFL, Lausanne */

package leon.synthesis.rules.unused

import leon.synthesis._

case object AsChoose extends Rule("As Choose") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    Some(solve(Solution.choose(p)))
  }
}

