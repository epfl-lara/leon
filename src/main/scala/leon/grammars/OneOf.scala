/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import purescala.Expressions.Expr
import purescala.TypeOps._
import purescala.Types.TypeTree

/** Generates one production rule for each expression in a sequence that has compatible type */
case class OneOf(inputs: Seq[Expr]) extends SimpleExpressionGrammar {
  def computeProductions(lab: TypeTree)(implicit ctx: LeonContext): Seq[Prod] = {
    inputs.collect {
      case i if isSubtypeOf(i.getType, lab.getType) =>
        terminal(i)
    }
  }
}
