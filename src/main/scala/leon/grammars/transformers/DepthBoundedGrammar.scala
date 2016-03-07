/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars
package transformers

/** Limits a grammar to a specific expression depth */
case class DepthBoundedGrammar[L](g: ExpressionGrammar[NonTerminal[L]], bound: Int) extends ExpressionGrammar[NonTerminal[L]] {
  def computeProductions(l: NonTerminal[L])(implicit ctx: LeonContext): Seq[Prod] = g.computeProductions(l).flatMap {
    case gen =>
      if (l.depth == Some(bound) && gen.isNonTerminal) {
        Nil
      } else if (l.depth.exists(_ > bound)) {
        Nil
      } else {
        List (
          gen.copy(subTrees = gen.subTrees.map(sl => sl.copy(depth = l.depth.map(_+1).orElse(Some(1)))))
        )
      }
  }
}
