/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

case class Union(gs: ExpressionGrammar*) extends ExpressionGrammar {
  val subGrammars: Seq[ExpressionGrammar] = gs.flatMap {
    case u: Union => u.subGrammars
    case g => Seq(g)
  }

  def generateProductions(implicit ctx: LeonContext) = {
    subGrammars.flatMap(_.generateProductions)
  }
}
