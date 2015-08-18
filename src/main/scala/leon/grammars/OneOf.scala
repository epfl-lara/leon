/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._
import purescala.Expressions._
import purescala.TypeOps._
import purescala.Constructors._

case class OneOf(inputs: Seq[Expr]) extends ExpressionGrammar[TypeTree] {
  def computeProductions(t: TypeTree)(implicit ctx: LeonContext): Seq[Gen] = {
    inputs.collect {
      case i if isSubtypeOf(i.getType, t) =>
        terminal(i)
    }
  }
}
