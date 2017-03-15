/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

/** The empty expression grammar */
case class Empty() extends ExpressionGrammar {
  def generateProductions(implicit ctx: LeonContext) = Nil
}
