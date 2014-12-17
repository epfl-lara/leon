/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import utils._
import utils.ExpressionGrammars._
import Witnesses._

case object CEGLESS extends CEGISLike[Label[String]]("CEGLESS") {
  def getParams(sctx: SynthesisContext, p: Problem) = {

    val TopLevelAnds(clauses) = p.ws

    val guides = clauses.collect {
      case Guide(e) => e
    }

    val inputs = p.as.map(_.toVariable)

    sctx.reporter.ifDebug { printer =>
      printer("Guides available:")
      for (g <- guides) {
        printer(" - "+g)
      }
    }

    val guidedGrammar = guides.map(SimilarTo(_, inputs.toSet, sctx, p)).foldLeft[ExpressionGrammar[Label[String]]](Empty())(_ || _)

    CegisParams(
      grammar = guidedGrammar,
      rootLabel = { (tpe: TypeTree) => Label(tpe, "G0") },
      maxUnfoldings = (0 +: guides.map(depth(_) + 1)).max
    )
  }
}



