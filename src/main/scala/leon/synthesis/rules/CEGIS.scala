/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import grammars._
import grammars.transformers._
import purescala.Types.TypeTree

/** Basic implementation of CEGIS that uses a naive grammar */
case object NaiveCEGIS extends CEGISLike[TypeTree]("Naive CEGIS") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    CegisParams(
      grammar = Grammars.default(sctx, p), // This limits type depth
      rootLabel = {(tpe: TypeTree) => tpe },
      optimizations = false
    )
  }
}

/** More advanced implementation of CEGIS that uses a less permissive grammar
  * and some optimizations
  */
case object CEGIS extends CEGISLike[TaggedNonTerm[TypeTree]]("CEGIS") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    val base = NaiveCEGIS.getParams(sctx,p).grammar
    CegisParams(
      grammar = TaggedGrammar(base),
      rootLabel = TaggedNonTerm(_, Tags.Top, 0, None),
      optimizations = true
    )
  }
}
