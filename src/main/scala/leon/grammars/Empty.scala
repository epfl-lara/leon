/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import purescala.Types.Typed

/** The empty expression grammar */
case class Empty[T <: Typed]() extends ExpressionGrammar[T] {
  def computeProductions(t: T)(implicit ctx: LeonContext): Seq[Prod] = Nil
}
