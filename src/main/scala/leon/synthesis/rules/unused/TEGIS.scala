/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules.unused

import purescala.Types._
import grammars._

case object TEGIS extends TEGISLike("TEGIS") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    TegisParams(
      grammar = Grammars.default(sctx, p),
      rootLabel = Label(_)
    )
  }
}
