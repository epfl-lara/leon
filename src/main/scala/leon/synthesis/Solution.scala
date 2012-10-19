package leon
package synthesis

import leon.purescala.Trees.Expr

// Defines a synthesis solution of the form:
// ⟨ P | T ⟩
case class Solution(pre: Expr, term: Expr) {
  override def toString = "⟨ "+pre+" | "+term+" ⟩" 
}

object Solution {
  def fromProblem(p: Problem): Solution =
    null
}
