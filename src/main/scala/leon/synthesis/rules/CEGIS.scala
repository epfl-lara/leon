/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import leon.grammars._
import leon.grammars.aspects._

/** Basic implementation of CEGIS that uses a naive grammar */
case object NaiveCEGIS extends CEGISLike("Naive CEGIS") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    CegisParams(
      grammar = grammars.default(sctx, p),
      rootLabel = Label(_),
      optimizations = false,
      sizes = List((1, sctx.settings.cegisMaxSize, sctx.settings.cegisMaxSize))
    )
  }
}

/** More advanced implementation of CEGIS that uses a less permissive grammar
  * and some optimizations
  */
case object CEGIS extends CEGISLike("CEGIS") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    val maxSize = sctx.settings.cegisMaxSize

    val sizesNew = for (s <- 1 to maxSize by 3) yield {
      (s, Math.min(s+2, maxSize), s+2)
    }

    val sizes = List((1, maxSize, 0));

    CegisParams(
      grammar = grammars.default(sctx, p),
      rootLabel = Label(_).withAspect(Tagged(Tags.Top, 0, None)),
      optimizations = true,
      sizes = sizes.toList
    )
  }
}
