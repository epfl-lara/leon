package leon
package synthesis

import leon.purescala.Trees._

// Defines a synthesis solution of the form:
// ⟨ P | T ⟩
case class Solution(pre: Expr, term: Expr) {
  override def toString = "⟨ "+pre+" | "+term+" ⟩" 
}

object Solution {
  def choose(p: Problem): Solution = Solution(BooleanLiteral(true), Choose(p.xs, p.phi))
}
