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

import evaluators.DefaultEvaluator

import Witnesses._

import solvers._

case object Split extends Rule("Split") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    if (hctx.searchDepth > 0) {
      return Nil
    }

    val ctx     = hctx.sctx.context
    val program = hctx.sctx.program

    val evaluator = new DefaultEvaluator(ctx, program)

    val TopLevelAnds(clauses) = p.ws

    val guides = clauses.collect {
      case Guide(expr) => expr
    }

    val wss = clauses.filter {
      case _: Guide => false
      case _ => true
    }

    def ws(g: Expr) = andJoin(Guide(g) +: wss)

    val simplify = Simplifiers.bestEffort(hctx.context, hctx.program)_

    val alts = guides.collect {
      case g @ IfExpr(c, thn, els) =>
        val sub1 = p.copy(ws = replace(Map(g -> thn), p.ws), pc = and(c, replace(Map(g -> thn), p.pc)), eb = p.qeb.filterIns(c))
        val sub2 = p.copy(ws = replace(Map(g -> els), p.ws), pc = and(Not(c), replace(Map(g -> els), p.pc)), eb = p.qeb.filterIns(Not(c)))

        val onSuccess: List[Solution] => Option[Solution] = { 
          case List(s1, s2) =>
            Some(Solution(or(s1.pre, s2.pre), s1.defs++s2.defs, IfExpr(c, s1.term, s2.term)))
          case _ =>
            None
        }

        Some(decomp(List(sub1, sub2), onSuccess, s"Guided If-Split on '${c.asString}'"))

      case m @ MatchExpr(scrut, cases) =>

        var pcSoFar: Seq[Expr] = Nil

        val infos = for (c <- cases) yield {
          val map  = mapForPattern(scrut, c.pattern)

          val thisCond = matchCaseCondition(scrut, c) // this case alone, without past cases
          val cond = andJoin(pcSoFar :+ thisCond) // with previous cases
          pcSoFar = pcSoFar :+ not(thisCond)

          val vars = map.toSeq.map(_._1)

          // Filter tests by the path-condition
          val eb2 = p.qeb.filterIns(cond)

          // Augment test with the additional variables and their valuations
          val ebF: (Seq[Expr] => List[Seq[Expr]]) = { (e: Seq[Expr]) =>
            val emap = (p.as zip e).toMap

            evaluator.eval(tupleWrap(vars.map(map)), emap).result.map { r =>
              e ++ unwrapTuple(r, vars.size)
            }.toList
          }

          val eb3 = if (vars.nonEmpty) {
            eb2.mapIns(ebF)
          } else {
            eb2
          }

          val newPc = andJoin(cond +: vars.map { id => equality(id.toVariable, map(id)) })

          (cond, Problem(p.as ++ vars, ws(c.rhs), and(p.pc, newPc), p.phi, p.xs, eb3))
        }

          val onSuccess = { (sols: List[Solution]) =>
            val term = MatchExpr(scrut, (cases zip sols).map {
              case (c, sol) => c.copy(rhs = sol.term)
            })

            val pres = (infos zip sols).collect {
              case ((cond, _), sol) if sol.pre != BooleanLiteral(true) =>
                and(cond, sol.pre)
            }

            Some(Solution(andJoin(pres), sols.map(_.defs).reduceLeft(_ ++ _), term, sols.forall(_.isTrusted)))
          }

          Some(
            decomp(infos.map(_._2).toList, onSuccess, s"Split match on '${scrut.asString}'")
          )

      case e =>
       None
    }

    alts.flatten
  }
}
