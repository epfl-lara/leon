/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis

import purescala.Common._
import purescala.Expressions._
import purescala.Types.{TypeTree,TupleType}
import purescala.Definitions._
import purescala.ExprOps._
import purescala.Constructors._
import purescala.Path

import leon.utils.Simplifiers

// Defines a synthesis solution of the form:
// ⟨ P | T ⟩
case class Solution(pre: Expr, defs: Set[FunDef], term: Expr, isTrusted: Boolean = true) extends Printable {

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
    letDef(defs.toList, guardedTerm)
  }
  
  def ifOnFunDef[T](originalFun: FunDef)(body: => T): T = {
    val saved = originalFun.body
    originalFun.body = Some(term)
    val res = body
    originalFun.body = saved
    res
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

  def toSimplifiedExpr(ctx: LeonContext, p: Program, pc: Path): Expr = {
    Simplifiers.bestEffort(ctx, p)(toExpr, pc)
  }
}

object Solution {

  def term(term: Expr, isTrusted: Boolean = true) = {
    Solution(BooleanLiteral(true), Set(), term, isTrusted)
  }

  def choose(p: Problem): Solution = {
    Solution(BooleanLiteral(true), Set(), Choose(Lambda(p.xs.map(ValDef), p.phi)))
  }

  def chooseComplete(p: Problem): Solution = {
    Solution(BooleanLiteral(true), Set(), Choose(Lambda(p.xs.map(ValDef), p.pc and p.phi)))
  }

  // Generate the simplest, wrongest solution, used for complexity lower bound
  def simplest(t: TypeTree): Solution = {
    Solution(BooleanLiteral(true), Set(), simplestValue(t))
  }

  def failed(implicit p: Problem): Solution = {
    val tpe = tupleTypeWrap(p.xs.map(_.getType))
    Solution(BooleanLiteral(false), Set(), Error(tpe, "Rule failed!"))
  }

  def UNSAT(implicit p: Problem): Solution = {
    val tpe = tupleTypeWrap(p.xs.map(_.getType))
    Solution(BooleanLiteral(false), Set(), Error(tpe, "Spec is UNSAT for this path!"))
  }
}
