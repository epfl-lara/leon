/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import purescala.Expressions.Expr
import purescala.TypeOps.normalizeType

/** Generates one production rule for each expression in a sequence that has compatible type */
case class OneOf(exprs: Seq[Expr]) extends SimpleExpressionGrammar {
  def generateSimpleProductions(implicit ctx: LeonContext) = {
    exprs.map { e =>
      sTerminal(normalizeType(e.getType), e)
    }
  }
}
