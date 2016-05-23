/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Expressions.Expr
import purescala.Types.Typed

case class Union(gs: Seq[ExpressionGrammar]) extends ExpressionGrammar {
  val subGrammars: Seq[ExpressionGrammar] = gs.flatMap {
    case u: Union => u.subGrammars
    case g => Seq(g)
  }

  def computeProductions(label: Label)(implicit ctx: LeonContext): Seq[ProductionRule[Label, Expr]] =
    subGrammars.flatMap(_.computeProductions(label))
}
