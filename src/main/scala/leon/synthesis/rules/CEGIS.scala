/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import grammars._
import grammars.Tags
import grammars.aspects._
import purescala.Types.TypeTree

/** Basic implementation of CEGIS that uses a naive grammar */
case object NaiveCEGIS extends CEGISLike("Naive CEGIS") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    CegisParams(
      grammar = Grammars.default(sctx, p),
      rootLabel = Label(_),
      optimizations = false
    )
  }
}

/** More advanced implementation of CEGIS that uses a less permissive grammar
  * and some optimizations
  */
case object CEGIS extends CEGISLike("CEGIS") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    CegisParams(
      grammar = Grammars.default(sctx, p),
      rootLabel = Label(_).withAspect(Tagged(Tags.Top, 0, None)),
      optimizations = true
    )
  }
}
