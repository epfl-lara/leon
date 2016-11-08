package leon
package grammars
package enumerators

import purescala.Expressions.Expr

trait GrammarEnumerator {
  protected val grammar: ExpressionGrammar
  def iterator(l: Label): Iterator[(Expr, Double)]
}
