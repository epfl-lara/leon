/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import leon.grammars._
import leon.grammars.aspects._

case object TEGIS extends TEGISLike("TEGIS") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    TegisParams(
      grammar = Grammars.default(sctx, p),
      rootLabel = Label(_).withAspect(Tagged(Tags.Top, 0, None))
    )
  }
}
