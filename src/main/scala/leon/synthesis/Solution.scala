/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis

import purescala.Trees._
import purescala.TypeTrees.{TypeTree,TupleType}
import purescala.Definitions._
import purescala.TreeOps._
import solvers.z3._

// Defines a synthesis solution of the form:
// ⟨ P | T ⟩
class Solution(val pre: Expr, val defs: Set[FunDef], val term: Expr) {
  override def toString = "⟨ "+pre+" | "+defs.mkString(" ")+" "+term+" ⟩" 

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

  def toSimplifiedExpr(ctx: LeonContext, p: Program): Expr = {
    val uninterpretedZ3 = new UninterpretedZ3SolverFactory(ctx, p)

    val simplifiers = List[Expr => Expr](
      simplifyTautologies(uninterpretedZ3)(_),
      simplifyLets _,
      decomposeIfs _,
      matchToIfThenElse _,
      simplifyPaths(uninterpretedZ3)(_),
      patternMatchReconstruction _,
      simplifyTautologies(uninterpretedZ3)(_),
      simplifyLets _,
      rewriteTuples _,
      (new ScopeSimplifier).transform _
    )

    simplifiers.foldLeft(toExpr){ (x, sim) => sim(x) }
  }
}

object Solution {
  def simplify(e: Expr) = simplifyLets(e)

  def apply(pre: Expr, defs: Set[FunDef], term: Expr) = {
    new Solution(simplify(pre), defs, simplify(term))
  }

  def unapply(s: Solution): Option[(Expr, Set[FunDef], Expr)] = if (s eq null) None else Some((s.pre, s.defs, s.term))

  def choose(p: Problem): Solution = {
    new Solution(BooleanLiteral(true), Set(), Choose(p.xs, p.phi).setType(TupleType(p.xs.map(_.getType))))
  }

  // Generate the simplest, wrongest solution, used for complexity lowerbound
  def basic(p: Problem): Solution = {
    new Solution(BooleanLiteral(true), Set(), Tuple(p.xs.map(id => simplestValue(id.getType))))
  }

  def simplest(t: TypeTree): Solution = {
    new Solution(BooleanLiteral(true), Set(), simplestValue(t))
  }
}
