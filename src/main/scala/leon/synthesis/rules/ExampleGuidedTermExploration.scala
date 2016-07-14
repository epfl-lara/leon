/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import leon.grammars._
import leon.grammars.aspects._

case object ExampleGuidedTermExploration extends ETELike("Example-guided Term Exploration") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    ETEParams(
      grammar = grammars.default(sctx, p),
      rootLabel = Label(_).withAspect(Tagged(Tags.Top, 0, None)),
      minSize = 1,
      maxSize = 5
    )
  }
}
