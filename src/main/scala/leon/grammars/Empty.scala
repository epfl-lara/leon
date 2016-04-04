/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

/** The empty expression grammar */
case class Empty() extends ExpressionGrammar {
  def computeProductions(l: Label)(implicit ctx: LeonContext) = Nil
}
