/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package repair
package rules

import synthesis._

import leon.utils.Simplifiers

import purescala.ScalaPrinter

import evaluators._

import purescala.Expressions._
import purescala.Definitions._
import purescala.Common._
import purescala.Types._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Extractors._

import Witnesses._

import solvers._

case object Focus extends Rule("Focus") {

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    if (hctx.searchDepth > 0) {
      return Nil
    }

    val fd      = hctx.ci.fd
    val ctx     = hctx.sctx.context
    val program = hctx.sctx.program

    val evaluator = new DefaultEvaluator(ctx, program)

    // Check how an expression behaves on tests
    //  - returns Some(true) if for all tests e evaluates to true
    //  - returns Some(false) if for all tests e evaluates to false
    //  - returns None otherwise
    def forAllTests(tests: Seq[Example])(e: Expr, env: Map[Identifier, Expr], evaluator: Evaluator): Option[Boolean] = {
      var soFar: Option[Boolean] = None

      tests.foreach { ex =>
        evaluator.eval(e, (p.as zip ex.ins).toMap ++ env) match {
          case EvaluationResults.Successful(BooleanLiteral(b)) => 
            soFar match {
              case None =>
                soFar = Some(b)
              case Some(`b`) =>
                /* noop */
              case _ => 
                return None
            }

          case e =>
            //println("Evaluator said "+e)
            return None
        }
      }

      soFar
    }

    val fdSpec = {
      val id = FreshIdentifier("res", fd.returnType)
      Let(id, fd.body.get,
        fd.postcondition.map(l => application(l, Seq(id.toVariable))).getOrElse(BooleanLiteral(true))
      )
    }

    def focus(p: Problem): Traversable[RuleInstantiation] = {
      val faTests = forAllTests(p.tb.invalids) _

      val TopLevelAnds(clauses) = p.ws

      val guides = clauses.collect {
        case Guide(expr) => expr
      }

      val wss = clauses.filter {
        case _: Guide => false
        case _ => true
      }

      def ws(g: Expr) = andJoin(Guide(g) +: wss)

      def testCondition(cond: Expr) = {
        val ndSpec = postMap {
          case c if c eq cond => Some(not(cond)) // Use reference equality
          case _ => None
        }(fdSpec)

        faTests(ndSpec, Map(), new RepairNDEvaluator(ctx, program, fd, cond))
      }

      guides.flatMap {
        case IfExpr(c, thn, els) =>
          testCondition(c) match {
            case Some(true) =>
              val cx = FreshIdentifier("cond", BooleanType)
              // Focus on condition
              val np = Problem(p.as, ws(c), p.pc, letTuple(p.xs, IfExpr(cx.toVariable, thn, els), p.phi), List(cx), p.tb.stripOuts)

              Some(decomp(List(np), termWrap(IfExpr(_, thn, els)), s"Focus on if-cond '$c'")(p))

            case _ =>
              // Try to focus on branches
              faTests(c, Map(), evaluator) match {
                case Some(true) =>
                  val np = Problem(p.as, ws(thn), and(p.pc, c), p.phi, p.xs, p.tbOps.filterIns(c))

                  Some(decomp(List(np), termWrap(IfExpr(c, _, els), c), s"Focus on if-then")(p))
                case Some(false) =>
                  val np = Problem(p.as, ws(els), and(p.pc, not(c)), p.phi, p.xs, p.tbOps.filterIns(not(c)))

                  Some(decomp(List(np), termWrap(IfExpr(c, thn, _), not(c)), s"Focus on if-else")(p))
                case None =>
                  // We cannot focus any further
                  None
              }
          }

        case MatchExpr(scrut, cases) =>
          var res: Option[Traversable[RuleInstantiation]] = None

          var pcSoFar: Seq[Expr] = Nil

          for (c <- cases if res.isEmpty) {
            val map  = mapForPattern(scrut, c.pattern)

            val thisCond = matchCaseCondition(scrut, c)
            val cond = andJoin(pcSoFar :+ thisCond)
            pcSoFar = pcSoFar :+ not(thisCond)

            // thisCond here is safe, because we focus we now that all tests have been false so far
            faTests(thisCond, map, evaluator) match {
              case Some(true) =>

                val vars = map.toSeq.map(_._1)

                // Filter tests by the path-condition
                val tb2 = p.tbOps.filterIns(cond)

                // Augment test with the additional variables and their valuations
                val tbF: (Seq[Expr] => List[Seq[Expr]]) = { (e: Seq[Expr]) =>
                  val emap = (p.as zip e).toMap

                  evaluator.eval(tupleWrap(vars.map(map)), emap).result.map { r =>
                    e ++ unwrapTuple(r, vars.size)
                  }.toList
                }

                val tb3 = if (vars.nonEmpty) {
                  tb2.mapIns(tbF)
                } else {
                  tb2
                }

                val newPc = andJoin(cond +: vars.map { id => equality(id.toVariable, map(id)) })

                val np = Problem(p.as ++ vars, ws(c.rhs), and(p.pc, newPc), p.phi, p.xs, tb3)

                res = Some(
                  Some(
                    decomp(List(np), termWrap(x => MatchExpr(scrut, cases.map {
                        case `c` => c.copy(rhs = x)
                        case c2  => c2
                      }), cond), s"Focus on match-case '${c.pattern}'")(p)
                  )
                )

              case Some(false) =>
                // continue until next case
              case None =>
                res = Some(Nil)
            }
          }

          res.getOrElse(Nil)


        case Let(id, value, body) =>
          val tbF: (Seq[Expr] => List[Seq[Expr]]) = { (e: Seq[Expr]) =>
            val map = (p.as zip e).toMap

            evaluator.eval(value, map).result.map { r =>
              e :+ r
            }.toList
          }

          val np = Problem(p.as :+ id, ws(body), and(p.pc, equality(id.toVariable, value)), p.phi, p.xs, p.tb.mapIns(tbF))

          Some(decomp(List(np), termWrap(Let(id, value, _)), s"Focus on let-body")(p))

        case _ => None
      }
    }

    def focusRec(is: Traversable[RuleInstantiation]): Traversable[RuleInstantiation] = {
      val res = is.flatMap { ri =>
        ri.apply(hctx) match {
          case RuleExpanded(subs) =>
            subs.flatMap(focus)
          case _ =>
            Nil
        }
      }

      if (res.isEmpty) {
        is
      } else {
        res
      }
    }

    focusRec(focus(p))
  }
}
