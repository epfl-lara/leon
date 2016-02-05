/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._

case class Union[T <: Typed](gs: Seq[ExpressionGrammar[T]]) extends ExpressionGrammar[T] {
  val subGrammars: Seq[ExpressionGrammar[T]] = gs.flatMap {
    case u: Union[T] => u.subGrammars
    case g => Seq(g)
  }

  def computeProductions(t: T)(implicit ctx: LeonContext): Seq[Gen] =
    subGrammars.flatMap(_.getProductions(t))
}
