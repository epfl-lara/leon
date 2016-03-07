/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars
package transformers

import leon.purescala.Types.Typed

/**
 * Embed a grammar Li->Expr within a grammar Lo->Expr
 * 
 * We rely on a bijection between Li and Lo labels
 */
case class EmbeddedGrammar[Ti <: Typed, To <: Typed](innerGrammar: ExpressionGrammar[Ti], iToo: Ti => To, oToi: To => Ti) extends ExpressionGrammar[To] {
  def computeProductions(t: To)(implicit ctx: LeonContext): Seq[Prod] = {
    innerGrammar.computeProductions(oToi(t)).map { innerGen =>
      innerGen.copy(subTrees = innerGen.subTrees.map(iToo))
    }
  }
}
