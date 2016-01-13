/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars
package transformers

import purescala.Expressions.Expr
import purescala.Types.TypeTree
import purescala.TypeOps.isSubtypeOf

/** Generates one production rule for each expression in a sequence that has compatible type */
case class OneOf(inputs: Seq[Expr]) extends ExpressionGrammar[TypeTree] {
  def computeProductions(t: TypeTree)(implicit ctx: LeonContext): Seq[Prod] = {
    inputs.collect {
      case i if isSubtypeOf(i.getType, t) =>
        terminal(i)
    }
  }
}
