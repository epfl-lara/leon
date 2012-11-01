package leon
package synthesis

import leon.purescala.Trees._
import leon.purescala.TreeOps.simplifyLets

// Defines a synthesis solution of the form:
// ⟨ P | T ⟩
class Solution(val pre: Expr, val term: Expr, val cost: Cost) {
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

  def complexity = Complexity.zero
}

object Solution {
  def choose(p: Problem, cost: Cost): Solution = new Solution(BooleanLiteral(true), Choose(p.xs, p.phi), cost)

  def none: Solution = throw new Exception("Unexpected failure to construct solution")

  def simplify(e: Expr) = simplifyLets(e)

  def apply(pre: Expr, term: Expr, cost: Cost) = {
    new Solution(simplify(pre), simplify(term), cost)
  }

  def unapply(s: Solution): Option[(Expr, Expr, Cost)] = if (s eq null) None else Some((s.pre, s.term, s.cost))
}
