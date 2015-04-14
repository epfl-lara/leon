/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package repair
package rules

import synthesis._

import leon.utils.Simplifiers

import purescala.Expressions._
import purescala.Definitions._
import purescala.Common._
import purescala.Types._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Constructors._

import Witnesses._

import solvers._

case object GuidedDecomp extends Rule("Guided Decomp") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    if (hctx.searchDepth > 0) {
      return Nil
    }

    val TopLevelAnds(clauses) = p.ws

    val guides = clauses.collect {
      case Guide(expr) => expr
    }

    val simplify = Simplifiers.bestEffort(hctx.context, hctx.program)_

    val alts = guides.collect {
      case g @ IfExpr(c, thn, els) =>
        val sub1 = p.copy(ws = replace(Map(g -> thn), p.ws), pc = and(c, replace(Map(g -> thn), p.pc)))
        val sub2 = p.copy(ws = replace(Map(g -> els), p.ws), pc = and(Not(c), replace(Map(g -> els), p.pc)))

        val onSuccess: List[Solution] => Option[Solution] = { 
          case List(s1, s2) =>
            Some(Solution(or(s1.pre, s2.pre), s1.defs++s2.defs, IfExpr(c, s1.term, s2.term)))
          case _ =>
            None
        }

        Some(decomp(List(sub1, sub2), onSuccess, s"Guided If-Split on '$c'"))

      case m @ MatchExpr(scrut0, _) =>

        val scrut = scrut0 match {
          case v : Variable => v
          case _ => Variable(FreshIdentifier("scrut", scrut0.getType, true))
        }
        var scrutCond: Expr = if (scrut == scrut0) BooleanLiteral(true) else Equals(scrut0, scrut)

        val fullMatch = if (isMatchExhaustive(m)) {
          m
        } else {
          m.copy(cases = m.cases :+ MatchCase(WildcardPattern(None), None, Error(m.getType, "unreachable in original program")))
        }

        val cs = fullMatch.cases

        val subs = for ((c, cond) <- cs zip matchCasePathConditions(fullMatch, List(p.pc))) yield {
          
          val localScrut = c.pattern.binder.map( Variable ) getOrElse scrut
          val scrutConstraint = if (localScrut == scrut) BooleanLiteral(true) else Equals(localScrut, scrut)
          val substs = patternSubstitutions(localScrut, c.pattern)
          
          val pc  = simplify(and(
            scrutCond,
            replace(Map(scrut0 -> scrut), replaceSeq(substs,scrutConstraint)),
            replace(Map(scrut0 -> scrut), replace(Map(m -> c.rhs), andJoin(cond)))
          ))
          val ws = replace(Map(m -> c.rhs), p.ws)
          val phi = replaceSeq(substs, p.phi)
          val free = variablesOf(and(pc, phi)) -- p.xs
          val asPrefix = p.as.filter(free)

          Problem(asPrefix ++ (free -- asPrefix), ws, pc, phi, p.xs)
        }

        val onSuccess: List[Solution] => Option[Solution] = { subs =>
          val cases = for ((c, s) <- cs zip subs) yield {
            c.copy(rhs = s.term)
          }

          Some(Solution(
            orJoin(subs.map(_.pre)),
            subs.map(_.defs).foldLeft(Set[FunDef]())(_ ++ _),
            if (scrut0 != scrut) Let(scrut.id, scrut0, matchExpr(scrut, cases))
            else matchExpr(scrut, cases),
            subs.forall(_.isTrusted)
          ))
        }

        Some(decomp(subs.toList, onSuccess, s"Guided Match-Split on '$scrut0'"))

      case e =>
       None
    }

    alts.flatten
  }
}
