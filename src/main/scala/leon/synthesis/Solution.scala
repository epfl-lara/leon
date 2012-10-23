package leon
package synthesis

import leon.purescala.Trees._

// Defines a synthesis solution of the form:
// ⟨ P | T ⟩
case class Solution(pre: Expr, term: Expr, score: Score = 0) {
  override def toString = "⟨ "+pre+" | "+term+" ⟩" 

  def toExpr = {
    if (pre == BooleanLiteral(true)) {
      term
    } else if (pre == BooleanLiteral(false)) {
      Error("Impossible program").setType(term.getType)
    } else {
      IfExpr(pre, term, Error("Precondition failed").setType(term.getType))
    }
  }
}

object Solution {
  def choose(p: Problem): Solution = Solution(BooleanLiteral(true), Choose(p.xs, p.phi), 0)

  def none: Solution = throw new Exception("Unexpected failure to construct solution")
}
