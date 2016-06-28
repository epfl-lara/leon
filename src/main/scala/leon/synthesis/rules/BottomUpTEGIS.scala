/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Types._
import leon.grammars._
import leon.grammars.aspects._

case object BottomUpTEGIS extends BottomUpTEGISLike("BU TEGIS") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    TegisParams(
      grammar = grammars.default(sctx, p),
      maxExpands = 4
    )
  }
}
