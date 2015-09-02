/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Expressions._
import ExprOps._
import Extractors._
import Constructors._

abstract class TransformerWithPC extends Transformer {
  type C

  protected val initC: C

  protected def register(cond: Expr, path: C): C

  protected def rec(e: Expr, path: C): Expr = e match {
    case Let(i, v, b) =>
      val se = rec(v, path)
      val sb = rec(b, register(Equals(Variable(i), se), path))
      Let(i, se, sb).copiedFrom(e)
      
    case p:Passes =>
      applyAsMatches(p,rec(_,path))

    case MatchExpr(scrut, cases) =>
      val rs = rec(scrut, path)

      var soFar = path

      MatchExpr(rs, cases.map { c =>
        val patternExprPos = conditionForPattern(rs, c.pattern, includeBinders = true)
        val patternExprNeg = conditionForPattern(rs, c.pattern, includeBinders = false)
        val map = mapForPattern(rs, c.pattern)
        val guardOrTrue = c.optGuard.getOrElse(BooleanLiteral(true))
        val guardMapped = replaceFromIDs(map, guardOrTrue)

        val subPath = register(and(patternExprPos, guardOrTrue), soFar)
        soFar = register(not(and(patternExprNeg, guardMapped)), soFar)
        
        MatchCase(c.pattern, c.optGuard, rec(c.rhs,subPath)).copiedFrom(c)

      }).copiedFrom(e)

    case IfExpr(cond, thenn, elze) =>
      val rc = rec(cond, path)

      IfExpr(rc, rec(thenn, register(rc, path)), rec(elze, register(Not(rc), path))).copiedFrom(e)

    case And(es) =>
      var soFar = path
      andJoin(for(e <- es) yield {
        val se = rec(e, soFar)
        soFar = register(se, soFar)
        se
      }).copiedFrom(e)

    case Or(es) =>
      var soFar = path
      orJoin(for(e <- es) yield {
        val se = rec(e, soFar)
        soFar = register(Not(se), soFar)
        se
      }).copiedFrom(e)

    case i @ Implies(lhs, rhs) =>
      val rc = rec(lhs, path)
      Implies(rc, rec(rhs, register(rc, path))).copiedFrom(i)

    case o @ Operator(es, builder) =>
      builder(es.map(rec(_, path))).copiedFrom(o)

    case _ =>
      sys.error("Expression "+e+" ["+e.getClass+"] is not extractable")
  }

  def transform(e: Expr): Expr = {
    rec(e, initC)
  }
}

