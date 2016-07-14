/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules
package unused

import purescala.Types._
import purescala.Extractors._
import Witnesses._
import leon.grammars._
import leon.grammars.aspects.{SimilarTo, DepthBound}

case object ExampleGuidedSimilarTermExploration extends ETELike("Example-guided Similar Term Expl.") {
  def getParams(sctx: SynthesisContext, p: Problem) = {

    val TopLevelAnds(clauses) = p.ws

    val guides = clauses.collect {
      case Guide(expr) => expr
    }

    sctx.reporter.ifDebug { printer =>
      printer("Guides available:")
      for (g <- guides) {
        printer(" - "+g)
      }
    }

    ETEParams(
      grammar = grammars.default(sctx, p),
      rootLabel = { (tpe: TypeTree) => Label(tpe).withAspect(DepthBound(2)).withAspect(SimilarTo(guides, sctx.functionContext)) },
      minSize = 1,
      maxSize = 5
    )
  }
}
