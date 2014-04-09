/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import purescala.Common._
import purescala.Trees._
import purescala.TypeTrees.{TypeTree,TupleType}
import purescala.Definitions._
import purescala.TreeOps._
import purescala.ScopeSimplifier
import solvers.z3._
import solvers._

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

  // Projects a solution (ignore several output variables)
  // 
  // e.g. Given solution for [[ a < .. > x1, x2, x3, x4 ]] and List(0, 1, 3)
  // It produces a solution for [[ a < .. > x1, x2, x4 ]]
  //
  // Indices are 0-indexed
  def project(indices: Seq[Int]): Solution = {
    val t = FreshIdentifier("t", true).setType(term.getType)
    val newTerm = Let(t, term, Tuple(indices.map(i => TupleSelect(t.toVariable, i+1))))

    Solution(pre, defs, newTerm)
  }


  def fullTerm =
    defs.foldLeft(term){ case (t, fd) => LetDef(fd, t) }

  def toSimplifiedExpr(ctx: LeonContext, p: Program): Expr = {
    val uninterpretedZ3 = SolverFactory(() => new UninterpretedZ3Solver(ctx, p))

    val simplifiers = List[Expr => Expr](
      simplifyTautologies(uninterpretedZ3)(_),
      simplifyLets _,
      decomposeIfs _,
      matchToIfThenElse _,
      simplifyPaths(uninterpretedZ3)(_),
      patternMatchReconstruction _,
      rewriteTuples _,
      evalGround(ctx, p),
      normalizeExpression _
    )

    val simple = { expr: Expr =>
      simplifiers.foldLeft(expr){ case (x, sim) => 
        sim(x)
      }
    }

    // Simplify first using stable simplifiers
    val s = fixpoint(simple)(toExpr)

    // Clean up ids/names
    (new ScopeSimplifier).transform(s)
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
