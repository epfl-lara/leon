/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import leon.grammars._
import leon.grammars.aspects._

/** Basic implementation of STE that uses a naive grammar */
case object UnoptimizedTermExploration extends STELike("Unoptimized Term Expl.") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    STEParams(
      grammar = grammars.default(sctx, p),
      rootLabel = Label(_),
      optimizations = false,
      sizes = List((1, sctx.settings.steMaxSize, sctx.settings.steMaxSize))
    )
  }
}

/** More advanced implementation of STE that uses a less permissive grammar
  * and some optimizations
  */
case object SymbolicTermExploration extends STELike("Symbolic Term Expl.") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    val maxSize = sctx.settings.steMaxSize

    //val sizesNew = for (s <- 1 to maxSize by 3) yield {
    //  (s, Math.min(s+2, maxSize), s+2)
    //}

    val sizes = List((1, maxSize, 0))

    STEParams(
      grammar = grammars.default(sctx, p),
      rootLabel = Label(_).withAspect(Tagged(Tags.Top, 0, None)),
      optimizations = true,
      sizes = sizes.toList
    )
  }
}
