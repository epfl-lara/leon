/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules.unused

import purescala.Types._
import purescala.Extractors._
import Witnesses._
import grammars._
import grammars.aspects.{SimilarTo, DepthBound}

case object TEGLESS extends TEGISLike("TEGLESS") {
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

    TegisParams(
      grammar = Grammars.default(sctx, p),
      rootLabel = { (tpe: TypeTree) => Label(tpe).withAspect(DepthBound(2)).withAspect(SimilarTo(guides)) }
    )
  }
}
