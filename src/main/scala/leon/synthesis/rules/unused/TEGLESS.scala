/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules.unused

import purescala.Types._
import purescala.Extractors._
import Witnesses._
import grammars._

case object TEGLESS extends TEGISLike[NonTerminal[String]]("TEGLESS") {
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

    val guidedGrammar = guides.map(SimilarTo(_, sctx, p)).foldLeft[ExpressionGrammar[NonTerminal[String]]](Empty())(_ || _)

    TegisParams(
      grammar = guidedGrammar,
      rootLabel = { (tpe: TypeTree) => NonTerminal(tpe, "G0") }
    )
  }
}



