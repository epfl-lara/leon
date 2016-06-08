/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.ExprOps._
import purescala.Types._
import purescala.Extractors._
import leon.grammars._
import leon.grammars.aspects._
import Witnesses._

case object CEGLESS extends CEGISLike("CEGLESS") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    val TopLevelAnds(clauses) = p.ws

    val guides = clauses.collect {
      case Guide(e) => e
    }

    sctx.reporter.ifDebug { printer =>
      printer("Guides available:")
      for (g <- guides) {
        printer(" - "+g.asString(sctx))
      }
    }

    CegisParams(
      grammar = grammars.default(sctx, p),
      rootLabel = (tpe: TypeTree) => Label(tpe).withAspect(DepthBound(2)).withAspect(SimilarTo(guides)),
      optimizations = false,
      maxSize = Some((0 +: guides.map(depth(_) + 1)).max)
    )
  }
}



