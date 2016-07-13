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

case object SimilarTermExploration extends STELike("Similar Term Expl.") {
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

    val maxSize = Math.min((0 +: guides.map(depth(_) + 2)).max, 5)

    STEParams(
      grammar = grammars.default(sctx, p, guides),
      rootLabel = (tpe: TypeTree) => Label(tpe).withAspect(DepthBound(2)).withAspect(SimilarTo(guides, sctx.functionContext)),
      optimizations = true,
      sizes = List((1, maxSize, 0))
    )
  }
}



