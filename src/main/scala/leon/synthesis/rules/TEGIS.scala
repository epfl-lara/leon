/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import leon.grammars._

case object TEGIS extends TEGISLike("TEGIS") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    TegisParams(
      grammar = grammars.default(sctx, p),
      rootLabel = Label(_)
    )
  }
}
