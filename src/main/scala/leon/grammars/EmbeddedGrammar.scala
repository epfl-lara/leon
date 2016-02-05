/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._
import purescala.Expressions._
import purescala.Constructors._

/**
 * Embed a grammar Li->Expr within a grammar Lo->Expr
 * 
 * We rely on a bijection between Li and Lo labels
 */
case class EmbeddedGrammar[Ti <: Typed, To <: Typed](innerGrammar: ExpressionGrammar[Ti], iToo: Ti => To, oToi: To => Ti) extends ExpressionGrammar[To] {
  def computeProductions(t: To)(implicit ctx: LeonContext): Seq[Gen] = {
    innerGrammar.computeProductions(oToi(t)).map { innerGen =>
      nonTerminal(innerGen.subTrees.map(iToo), innerGen.builder)
    }
  }
}
