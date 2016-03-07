/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Types._
import purescala.Extractors._
import utils._
import Witnesses._
import grammars._

case object TEGLESS extends TEGISLike[NonTerminal[String]]("TEGLESS") {
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

    val guidedGrammar = guides.map(SimilarTo(_, inputs.toSet, sctx, p)).foldLeft[ExpressionGrammar[NonTerminal[String]]](Empty())(_ || _)

    TegisParams(
      grammar = guidedGrammar,
      rootLabel = { (tpe: TypeTree) => NonTerminal(tpe, "G0") }
    )
  }
}



