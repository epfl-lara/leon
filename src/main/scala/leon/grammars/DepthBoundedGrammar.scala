/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

case class DepthBoundedGrammar[T](g: ExpressionGrammar[NonTerminal[T]], bound: Int) extends ExpressionGrammar[NonTerminal[T]] {
  def computeProductions(l: NonTerminal[T])(implicit ctx: LeonContext): Seq[Gen] = g.computeProductions(l).flatMap {
    case gen =>
      if (l.depth == Some(bound) && gen.subTrees.nonEmpty) {
        Nil
      } else if (l.depth.exists(_ > bound)) {
        Nil
      } else {
        List (
          nonTerminal(gen.subTrees.map(sl => sl.copy(depth = l.depth.map(_+1).orElse(Some(1)))), gen.builder)
        )
      }
  }
}
