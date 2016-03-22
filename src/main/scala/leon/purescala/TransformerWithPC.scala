/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Expressions._
import ExprOps._
import Extractors._
import Constructors._

/** Traverses/ transforms expressions with path condition awareness.
  *
  * Path condition representation is left generic (type [[C]])
  */
abstract class TransformerWithPC extends Transformer {

  /** The type of the path condition */
  type C

  /** The initial path condition */
  protected val initC: C

  /** Register a new expression to a path condition */
  protected def register(cond: Expr, path: C): C

  protected def rec(e: Expr, path: C): Expr = e match {
    case Let(i, v, b) =>
      val se = rec(v, path)
      val sb = rec(b, register(Equals(Variable(i), se), path))
      Let(i, se, sb).copiedFrom(e)

    case Ensuring(req@Require(pre, body), lam@Lambda(Seq(arg), post)) =>
      val spre = rec(pre, path)
      val sbody = rec(body, register(spre, path))
      val spost = rec(post, register(
        and(spre, Equals(arg.toVariable, sbody)),
        path
      ))
      Ensuring(
        Require(spre, sbody).copiedFrom(req),
        Lambda(Seq(arg), spost).copiedFrom(lam)
      ).copiedFrom(e)

    case Ensuring(body, lam@Lambda(Seq(arg), post)) =>
      val sbody = rec(body, path)
      val spost = rec(post, register(Equals(arg.toVariable, sbody), path))
      Ensuring(
        sbody,
        Lambda(Seq(arg), spost).copiedFrom(lam)
      ).copiedFrom(e)

    case Require(pre, body) =>
      val sp = rec(pre, path)
      val sb = rec(body, register(sp, path))
      Require(sp, sb).copiedFrom(e)

    //@mk: TODO Discuss if we should include asserted predicates in the pc
    //case Assert(pred, err, body) =>
    //  val sp = rec(pred, path)
    //  val sb = rec(body, register(sp, path))
    //  Assert(sp, err, sb).copiedFrom(e)

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

