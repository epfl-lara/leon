/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._

case class Empty[T <% Typed]() extends ExpressionGrammar[T] {
  def computeProductions(t: T)(implicit ctx: LeonContext): Seq[Gen] = Nil
}
