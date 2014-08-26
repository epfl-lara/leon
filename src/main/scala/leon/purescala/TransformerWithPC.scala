/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import Trees._
import TreeOps._
import Extractors._

abstract class TransformerWithPC extends Transformer {
  type C

  protected val initC: C

  protected def register(cond: Expr, path: C): C

  protected def rec(e: Expr, path: C): Expr = e match {
    case Let(i, e, b) =>
      val se = rec(e, path)
      val sb = rec(b, register(Equals(Variable(i), se), path))
      Let(i, se, sb).copiedFrom(e)

    case MatchExpr(scrut, cases) =>
      val rs = rec(scrut, path)

      var soFar = path

      MatchExpr(rs, cases.map { c =>
        val patternExprPos = conditionForPattern(rs, c.pattern, includeBinders = true)
        val patternExprNeg = conditionForPattern(rs, c.pattern, includeBinders = false)

        val subPath = register(patternExprPos, soFar)
        soFar = register(Not(patternExprNeg), soFar)

        c match {
          case SimpleCase(p, rhs) =>
            SimpleCase(p, rec(rhs, subPath)).copiedFrom(c)
          case GuardedCase(p, g, rhs) =>
            GuardedCase(p, g, rec(rhs, subPath)).copiedFrom(c)
        }
      }).copiedFrom(e)

    case LetTuple(is, e, b) =>
      val se = rec(e, path)
      val sb = rec(b, register(Equals(Tuple(is.map(Variable(_))), se), path))
      LetTuple(is, se, sb).copiedFrom(e)

    case IfExpr(cond, thenn, elze) =>
      val rc = rec(cond, path)

      IfExpr(rc, rec(thenn, register(rc, path)), rec(elze, register(Not(rc), path))).copiedFrom(e)

    case And(es) =>
      var soFar = path
      And(for(e <- es) yield {
        val se = rec(e, soFar)
        soFar = register(se, soFar)
        se
      }).copiedFrom(e)

    case Or(es) =>
      var soFar = path
      Or(for(e <- es) yield {
        val se = rec(e, soFar)
        soFar = register(Not(se), soFar)
        se
      }).copiedFrom(e)

    case o @ UnaryOperator(e, builder) =>
      builder(rec(e, path)).copiedFrom(o)

    case o @ BinaryOperator(e1, e2, builder) =>
      builder(rec(e1, path), rec(e2, path)).copiedFrom(o)

    case o @ NAryOperator(es, builder) =>
      builder(es.map(rec(_, path))).copiedFrom(o)

    case t : Terminal => t

    case _ =>
      sys.error("Expression "+e+" ["+e.getClass+"] is not extractable")
  }

  def transform(e: Expr): Expr = {
    rec(e, initC)
  }
}

