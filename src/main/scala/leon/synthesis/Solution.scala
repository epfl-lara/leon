package leon
package synthesis

import leon.purescala.Trees._
import leon.purescala.Definitions._
import leon.purescala.TreeOps._
import aographs._

// Defines a synthesis solution of the form:
// ⟨ P | T ⟩
class Solution(val pre: Expr, val defs: Set[FunDef], val term: Expr) extends AOSolution {
  override def toString = "⟨ "+pre+" | "+defs.mkString(" ")+" "+term+" ⟩" 

  val cost: AOCost = null

  def toExpr = {
    val result = if (pre == BooleanLiteral(true)) {
      term
    } else if (pre == BooleanLiteral(false)) {
      Error("Impossible program").setType(term.getType)
    } else {
      IfExpr(pre, term, Error("Precondition failed").setType(term.getType))
    }

    defs.foldLeft(result){ case (t, fd) => LetDef(fd, t) }
  }

  def fullTerm =
    defs.foldLeft(term){ case (t, fd) => LetDef(fd, t) }
}

object Solution {

  def simplify(e: Expr) = simplifyLets(e)

  def apply(pre: Expr, defs: Set[FunDef], term: Expr) = {
    new Solution(simplify(pre), defs, simplify(term))
  }

  def unapply(s: Solution): Option[(Expr, Set[FunDef], Expr)] = if (s eq null) None else Some((s.pre, s.defs, s.term))

  def choose(p: Problem): Solution = {
    new Solution(BooleanLiteral(true), Set(), Choose(p.xs, p.phi))
  }

  // Generate the simplest, wrongest solution, used for complexity lowerbound
  def basic(p: Problem): Solution = {
    new Solution(BooleanLiteral(true), Set(), Tuple(p.xs.map(id => simplestValue(id.getType))))
  }

  def simplest: Solution = {
    new Solution(BooleanLiteral(true), Set(), BooleanLiteral(true))
  }

  def none: Solution = {
    throw new Exception("Unexpected failure to construct solution")
  }
}
