package leon
package synthesis

import leon.purescala.Trees._
import leon.purescala.TreeOps.simplifyLets

// Defines a synthesis solution of the form:
// ⟨ P | T ⟩
class Solution(val pre: Expr, val term: Expr) {
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

  def score: Score = 10
}

object Solution {
  def choose(p: Problem): Solution = new Solution(BooleanLiteral(true), Choose(p.xs, p.phi)) {
    override def score: Score = 0
  }

  def none: Solution = throw new Exception("Unexpected failure to construct solution")

  def simplify(e: Expr) = simplifyLets(e)

  def apply(pre: Expr, term: Expr) = {
    new Solution(simplify(pre), simplify(term))
  }

  def unapply(s: Solution): Option[(Expr, Expr)] = if (s eq null) None else Some((s.pre, s.term))
}
