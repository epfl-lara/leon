/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import grammars._
import grammars.transformers._
import purescala.Types.TypeTree

case object CEGIS extends CEGISLike[TypeTree]("CEGIS") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    CegisParams(
      grammar = Grammars.typeDepthBound(Grammars.default(sctx, p), 2), // This limits type depth
      rootLabel = {(tpe: TypeTree) => tpe },
      maxUnfoldings = 12,
      optimizations = false
    )
  }
}

case object CEGIS2 extends CEGISLike[TaggedNonTerm[TypeTree]]("CEGIS2") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    val base = CEGIS.getParams(sctx,p).grammar
    CegisParams(
      grammar = TaggedGrammar(base),
      rootLabel = TaggedNonTerm(_, Tags.Top, 0, None),
      maxUnfoldings = 12,
      optimizations = true
    )
  }
}