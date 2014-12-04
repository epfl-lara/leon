/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TypeTrees._
import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import utils._
import utils.ExpressionGrammars._

case object CEGLESS extends CEGISLike[Label[String]]("CEGLESS") {
  override val maxUnfoldings = 1000;

  def getGrammar(sctx: SynthesisContext, p: Problem) = {

    val TopLevelAnds(clauses) = p.pc

    val guide = sctx.program.library.guide.get

    val guides = clauses.collect {
      case FunctionInvocation(TypedFunDef(`guide`, _), Seq(expr)) => expr
    }

    val inputs = p.as.map(_.toVariable)

    val guidedGrammar = guides.map(SimilarTo(_, inputs.toSet, Set(sctx.functionContext))).foldLeft[ExpressionGrammar[Label[String]]](Empty())(_ || _)

    guidedGrammar
  }

  def getGrammarLabel(id: Identifier): Label[String] = Label(id.getType, "G0")
}



