/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis

import purescala.Common._
import purescala.Expressions._
import purescala.Types.{TypeTree,TupleType}
import purescala.Definitions._
import purescala.ExprOps._
import purescala.Constructors._

import leon.utils.Simplifiers

// Defines a synthesis solution of the form:
// ⟨ P | T ⟩
class Solution(val pre: Expr, val defs: Set[FunDef], val term: Expr, val isTrusted: Boolean = true) {

  def asString(implicit ctx: LeonContext) = {
    "⟨ "+pre.asString+" | "+defs.map(_.asString).mkString(" ")+" "+term.asString+" ⟩" 
  }

  def guardedTerm = {
    if (pre == BooleanLiteral(true)) {
      term
    } else if (pre == BooleanLiteral(false)) {
      Error(term.getType, "Impossible program")
    } else {
      IfExpr(pre, term, Error(term.getType, "Precondition failed"))
    }
  }

  def toExpr = {
    defs.foldLeft(guardedTerm){ case (t, fd) => LetDef(fd, t) }
  }

  // Projects a solution (ignore several output variables)
  // 
  // e.g. Given solution for [[ a < .. > x1, x2, x3, x4 ]] and List(0, 1, 3)
  // It produces a solution for [[ a < .. > x1, x2, x4 ]]
  //
  // Indices are 0-indexed
  def project(indices: Seq[Int]): Solution = {
    term.getType match {
      case TupleType(ts) =>
        val t = FreshIdentifier("t", term.getType, true)
        val newTerm = Let(t, term, tupleWrap(indices.map(i => tupleSelect(t.toVariable, i+1, indices.size))))

        Solution(pre, defs, newTerm)
      case _ =>
        this
    }
  }


  def toSimplifiedExpr(ctx: LeonContext, p: Program): Expr = {
    Simplifiers.bestEffort(ctx, p)(toExpr)
  }
}

object Solution {
  def simplify(e: Expr) = simplifyLets(e)

  def apply(pre: Expr, defs: Set[FunDef], term: Expr, isTrusted: Boolean = true) = {
    new Solution(simplify(pre), defs, simplify(term), isTrusted)
  }

  def term(term: Expr, isTrusted: Boolean = true) = {
    new Solution(BooleanLiteral(true), Set(), simplify(term), isTrusted)
  }

  def unapply(s: Solution): Option[(Expr, Set[FunDef], Expr)] = if (s eq null) None else Some((s.pre, s.defs, s.term))

  def choose(p: Problem): Solution = {
    new Solution(BooleanLiteral(true), Set(), Choose(Lambda(p.xs.map(ValDef(_)), p.phi)))
  }

  def chooseComplete(p: Problem): Solution = {
    new Solution(BooleanLiteral(true), Set(), Choose(Lambda(p.xs.map(ValDef(_)), and(p.pc, p.phi))))
  }

  // Generate the simplest, wrongest solution, used for complexity lowerbound
  def basic(p: Problem): Solution = {
    simplest(p.outType)
  }

  def simplest(t: TypeTree): Solution = {
    new Solution(BooleanLiteral(true), Set(), simplestValue(t))
  }

  def failed(implicit p: Problem): Solution = {
    val tpe = tupleTypeWrap(p.xs.map(_.getType))
    Solution(BooleanLiteral(false), Set(), Error(tpe, "Rule failed!"))
  }

  def UNSAT(implicit p: Problem): Solution = {
    val tpe = tupleTypeWrap(p.xs.map(_.getType))
    Solution(BooleanLiteral(false), Set(), Error(tpe, p.phi+" is UNSAT!"))
  }
}
