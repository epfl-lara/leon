/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Types._
import purescala.Extractors._
import utils._
import utils.ExpressionGrammars._
import Witnesses._

case object TEGLESS extends TEGISLike[Label[String]]("TEGLESS") {
  def getParams(sctx: SynthesisContext, p: Problem) = {

    val TopLevelAnds(clauses) = p.ws

    val guides = clauses.collect {
      case Guide(expr) => expr
    }

    val inputs = p.as.map(_.toVariable)

    sctx.reporter.ifDebug { printer =>
      printer("Guides available:")
      for (g <- guides) {
        printer(" - "+g)
      }
    }

    val guidedGrammar = guides.map(SimilarTo(_, inputs.toSet, sctx, p)).foldLeft[ExpressionGrammar[Label[String]]](Empty())(_ || _)

    TegisParams(
      grammar = guidedGrammar,
      rootLabel = { (tpe: TypeTree) => Label(tpe, "G0") }
    )
  }
}



