/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Expressions._
import Constructors._
import Extractors._
import ExprOps._

/** Traverses/ transforms expressions with path condition awareness.
  *
  * As lets cannot be encoded as Equals due to types for which equality
  * is not well-founded, path conditions reconstruct lets around the
  * final condition one wishes to verify through [[Path.getClause]].
  */
abstract class TransformerWithPC extends Transformer {

  /** The initial path condition */
  protected val initPath: Path

  protected def rec(e: Expr, path: Path): Expr = e match {
    case Let(i, v, b) =>
      val se = rec(v, path)
      val sb = rec(b, path withBinding (i -> se))
      Let(i, se, sb).copiedFrom(e)

    case Ensuring(req @ Require(pre, body), lam @ Lambda(Seq(arg), post)) =>
      val spre = rec(pre, path)
      val sbody = rec(body, path withCond spre)
      val spost = rec(post, path withCond spre withBinding (arg.id -> sbody))
      Ensuring(
        Require(spre, sbody).copiedFrom(req),
        Lambda(Seq(arg), spost).copiedFrom(lam)
      ).copiedFrom(e)

    case Ensuring(body, lam @ Lambda(Seq(arg), post)) =>
      val sbody = rec(body, path)
      val spost = rec(post, path withBinding (arg.id -> sbody))
      Ensuring(
        sbody,
        Lambda(Seq(arg), spost).copiedFrom(lam)
      ).copiedFrom(e)

    case Require(pre, body) =>
      val sp = rec(pre, path)
      val sb = rec(body, path withCond pre)
      Require(sp, sb).copiedFrom(e)

    //@mk: TODO Discuss if we should include asserted predicates in the pc
    //case Assert(pred, err, body) =>
    //  val sp = rec(pred, path)
    //  val sb = rec(body, register(sp, path))
    //  Assert(sp, err, sb).copiedFrom(e)

    case p: Passes =>
      applyAsMatches(p, rec(_,path))

    case MatchExpr(scrut, cases) =>
      val rs = rec(scrut, path)

      var soFar = path

      MatchExpr(rs, cases.map { c =>
        val patternPathPos = conditionForPattern(rs, c.pattern, includeBinders = true)
        val patternPathNeg = conditionForPattern(rs, c.pattern, includeBinders = false)
        val map = mapForPattern(rs, c.pattern)
        val guardOrTrue = c.optGuard.getOrElse(BooleanLiteral(true))
        val guardMapped = replaceFromIDs(map, guardOrTrue)

        val subPath = soFar merge (patternPathPos withCond guardOrTrue)
        soFar = soFar merge (patternPathNeg withCond guardMapped).negate

        MatchCase(c.pattern, c.optGuard, rec(c.rhs, subPath)).copiedFrom(c)
      }).copiedFrom(e)

    case IfExpr(cond, thenn, elze) =>
      val rc = rec(cond, path)
      IfExpr(rc, rec(thenn, path withCond rc), rec(elze, path withCond Not(rc))).copiedFrom(e)

    case And(es) =>
      var soFar = path
      andJoin(for(e <- es) yield {
        val se = rec(e, soFar)
        soFar = soFar withCond se
        se
      }).copiedFrom(e)

    case Or(es) =>
      var soFar = path
      orJoin(for(e <- es) yield {
        val se = rec(e, soFar)
        soFar = soFar withCond Not(se)
        se
      }).copiedFrom(e)

    case i @ Implies(lhs, rhs) =>
      val rc = rec(lhs, path)
      Implies(rc, rec(rhs, path withCond rc)).copiedFrom(i)

    case o @ Operator(es, builder) =>
      builder(es.map(rec(_, path))).copiedFrom(o)

    case _ =>
      sys.error("Expression "+e+" ["+e.getClass+"] is not extractable")
  }

  def transform(e: Expr): Expr = {
    rec(e, initPath)
  }
}

