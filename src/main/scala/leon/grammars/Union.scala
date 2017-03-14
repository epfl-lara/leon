/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Expressions.Expr

import utils.MapUtils

case class Union(gs: Seq[ExpressionGrammar]) extends ExpressionGrammar {
  val subGrammars: Seq[ExpressionGrammar] = gs.flatMap {
    case u: Union => u.subGrammars
    case g => Seq(g)
  }

  val staticProductions  = subGrammars.map(_.staticProductions).reduceLeft(MapUtils.union)
  val genericProductions = subGrammars.map(_.genericProductions).reduceLeft(_ ++ _)
}
