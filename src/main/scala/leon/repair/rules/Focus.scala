/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package repair
package rules

import purescala.Definitions.Program
import purescala.Path
import purescala.Expressions._
import purescala.Common._
import purescala.Types._
import purescala.ExprOps._
import purescala.Constructors._
import purescala.Extractors._

import collection.mutable.ArrayBuffer

import evaluators._

import synthesis._
import Witnesses._
import graph.AndNode

case object Focus extends PreprocessingRule("Focus") {

  // This evaluator does two things:
  // 1) Treats nd like a non-deterministic value
  // 2) Unless it is wrapped in a Not, in which case it is treated normally.
  //    This is because when we call it to evaluate the condition we want the first call to be negated
  //    deterministically, because the test is minimized and nd will always fail at top-level
  private class RepairNDEvaluator(ctx: LeonContext, prog: Program, nd: Expr) extends StreamEvaluator(ctx, prog) {
    override def e(expr: Expr)(implicit rctx: RC, gctx: GC): Stream[Expr] = expr match {
      case Not(c) if c eq nd =>
        // This is a hack: We know the only way nd is wrapped within a Not is if it is NOT within
        // a recursive call. So we need to treat it deterministically at this point...
        super.e(c) collect { case BooleanLiteral(b) => BooleanLiteral(!b) }
      case c if c eq nd =>
        valuesOf(c.getType)
      case other =>
        super.e(other)
    }
  }


  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    hctx.parentNode match {
      case Some(an: AndNode) if an.ri.rule == Focus =>
        // We proceed as usual
      case Some(_) =>
        return None;
      case _ =>
        // We proceed as usual
    }

    val qeb = p.qebFiltered

    val program = hctx.program

    val evaluator = new DefaultEvaluator(hctx, program)

    val timers = hctx.timers.synthesis.instantiations.Focus

    // Check how an expression behaves on tests
    //  - returns Some(true) if for all tests e evaluates to true
    //  - returns Some(false) if for all tests e evaluates to false
    //  - returns None otherwise
    var invalids = qeb.invalids

    def forAllTests(e: Expr, env: Map[Identifier, Expr], evaluator: Evaluator): Option[Boolean] = {
      var soFar: Option[Boolean] = None

      qeb.invalids.foreach { ex =>
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

    def existsFailing(e: Expr, env: Map[Identifier, Expr], evaluator: DeterministicEvaluator, last: Boolean): Boolean = {
      var foundOne = false;
      var newInvalids = new ArrayBuffer[Example]();

      for (ex <- invalids) {
        val res = evaluator.eval(e, (p.as zip ex.ins).toMap ++ env).result match {
          case Some(BooleanLiteral(b)) =>
            b
          case _ =>
            true
        }

        if (res) {
          foundOne = true;
          if (last) {
            return true;
          }
        } else {
          newInvalids += ex
        }
      }

      invalids = newInvalids
      foundOne
    }


    val TopLevelAnds(clauses) = p.ws

    val guides = clauses.collect {
      case Guide(expr) => expr
    }

    val wss = clauses.filter {
      case _: Guide => false
      case _ => true
    }

    def ws(g: Expr) = andJoin(Guide(g) +: wss)

    guides.flatMap {
      case g @ IfExpr(c, thn, els) =>
        timers.If.timed{

        val spec = letTuple(p.xs, IfExpr(Not(c), thn, els), p.phi)
        // Try to focus on condition:
        //   Does there exists path for non-deterministic 'c' which satisfies phi?
        //   (Top-level is deterministically negated, because we know test is minimized)
        val condTesting = forAllTests(spec, Map(), new AngelicEvaluator(new RepairNDEvaluator(hctx, program, c)))
        condTesting match {
          case Some(true) =>
            val cx = FreshIdentifier("cond", BooleanType)
            // Focus on condition
            val np = Problem(p.as, ws(c), p.pc, letTuple(p.xs, IfExpr(cx.toVariable, thn, els), p.phi), List(cx), qeb.stripOuts)

            Some(decomp(List(np), termWrap(IfExpr(_, thn, els)), s"Focus on if-cond '${c.asString}'")(p))

          case _ =>
            // Try to focus on branches
            forAllTests(c, Map(), evaluator) match {
              case Some(true) =>
                val np = Problem(p.as, ws(thn), p.pc withCond c, p.phi, p.xs, qeb.filterIns(c))
                val onSuccess = wrap( pre => or(and(c, pre), not(c)), IfExpr(c, _, els))
                Some(decomp(List(np), onSuccess, s"Focus on if-then")(p))

              case Some(false) =>
                val np = Problem(p.as, ws(els), p.pc withCond not(c), p.phi, p.xs, qeb.filterIns(not(c)))
                val onSuccess = wrap( pre => or(c, and(not(c), pre)), IfExpr(c, thn, _))
                Some(decomp(List(np), onSuccess, s"Focus on if-else")(p))

              case None =>
                // We split
                val sub1 = p.copy(ws = ws(thn), pc = p.pc map (replace(Map(g -> thn), _)) withCond     c , eb = qeb.filterIns(c))
                val sub2 = p.copy(ws = ws(els), pc = p.pc map (replace(Map(g -> thn), _)) withCond Not(c), eb = qeb.filterIns(Not(c)))

                val onSuccess: List[Solution] => Option[Solution] = { 
                  case List(s1, s2) =>
                    Some(Solution(or(and(c, s1.pre), and(not(c), s2.pre)), s1.defs++s2.defs, IfExpr(c, s1.term, s2.term)))
                  case _ =>
                    None
                }

                Some(decomp(List(sub1, sub2), onSuccess, s"Focus on both branches of '${c.asString}'"))
            }
        }
        }

      case MatchExpr(scrut, cases) =>
        var pcSoFar = Path.empty

        timers.Match.start()
        // Generate subproblems for each match-case that fails at least one test.
        var casesInfos = for (c <- cases) yield {
          val map  = mapForPattern(scrut, c.pattern)

          val thisCond = matchCaseCondition(scrut, c)
          val prevPCSoFar = pcSoFar
          val cond = pcSoFar merge thisCond
          pcSoFar = pcSoFar merge thisCond.negate

          val subP = if (existsFailing(cond.toClause, map, evaluator, false)) {

            val vars = map.keys.toSeq

            val (p2e, _) = patternToExpression(c.pattern, scrut.getType)

            val substAs = ((scrut, p2e) match {
              case (Variable(i), _) if p.as.contains(i) => Seq(i -> p2e)
              case (Tuple(as), Tuple(tos)) =>
                val res = as.zip(tos) collect {
                  case (Variable(i), to) if p.as.contains(i) => i -> to
                }
                if (res.size == as.size) res else Nil
              case _ => Nil
            }).toMap

            if (substAs.nonEmpty) {
              timers.Match.filterIns.start()
              val subst = replaceFromIDs(substAs, _: Expr)
              // FIXME intermediate binders??
              val newAs = (p.as diff substAs.keys.toSeq) ++ vars
              val newPc = (p.pc merge prevPCSoFar) map subst
              val newWs = subst(ws(c.rhs))
              val newPhi = subst(p.phi)
              val eb2 = qeb.filterIns(cond.toClause)
              val ebF: Seq[(Identifier, Expr)] => List[Seq[Expr]] = { (ins: Seq[(Identifier, Expr)]) =>
                val eval = evaluator.eval(tupleWrap(vars map Variable), map ++ ins)
                val insWithout = ins.collect{ case (id, v) if !substAs.contains(id) => v }
                eval.result.map(r => insWithout ++ unwrapTuple(r, vars.size)).toList
              }
              val newEb = eb2.flatMapIns(ebF)
              timers.Match.filterIns.stop()
              Some(Problem(newAs, newWs, newPc, newPhi, p.xs, newEb))
            } else {
              timers.Match.filterIns.start()
              // Filter tests by the path-condition
              val eb2 = qeb.filterIns(cond.toClause)

              val newPc = cond withBindings vars.map(id => id -> map(id))
              timers.Match.filterIns.stop()

              Some(Problem(p.as, ws(c.rhs), p.pc merge newPc, p.phi, p.xs, eb2))
            }
          } else {
            None
          }

          c -> (subP, cond)
        }

        // Check if the match might be missing a case? (we check if one test
        // goes to no defined cases)
        val elsePc = pcSoFar

        if (existsFailing(elsePc.toClause, Map(), evaluator, true)) {
          val newCase    = MatchCase(WildcardPattern(None), None, NoTree(scrut.getType))

          val qeb2 = qeb.filterIns(elsePc.toClause)

          val newProblem = Problem(p.as, andJoin(wss), p.pc merge elsePc, p.phi, p.xs, qeb2)

          casesInfos :+= (newCase -> (Some(newProblem), elsePc))
        }

        timers.Match.stop()

        // Is there at least one subproblem?
        if (casesInfos.exists(_._2._1.isDefined)) {
          val (cases, nps, pcs) = casesInfos.collect {
            case (c, (Some(p), pc)) => (c, p, pc)
          }.unzip3

          val restPcs = casesInfos.collect {
            case (_, (None, pc)) => pc.toClause
          }

          val appName = s"Focus on match-cases ${cases.map(c => "'"+c.pattern.asString+"'").mkString(", ")}"

          val onSuccess: List[Solution] => Option[Solution] = { 
            case ss =>
              val pres = (pcs zip cases zip ss).map {
                case ((pc, cse), s) =>
                  pc and replaceFromIDs(mapForPattern(scrut, cse.pattern), s.pre)
              }
              val solsMap = (cases zip ss).toMap
              val expr = MatchExpr(scrut, casesInfos.map { case (c, _) => solsMap.get(c) match {
                case Some(s) =>
                  c.copy(rhs = s.term)
                case None =>
                  c
              }})

              Some(Solution(orJoin(restPcs ++ pres), ss.map(_.defs).reduceLeft(_ ++ _), expr))
          }

          Some(decomp(nps.toList, onSuccess, appName)(p))
        } else {
          None
        }

      case Let(id, value, body) =>
        val ebF: (Seq[Expr] => List[Seq[Expr]]) = { (e: Seq[Expr]) =>
          val map = (p.as zip e).toMap

          evaluator.eval(value, map).result.map { r =>
            e :+ r
          }.toList
        }

        val np = Problem(p.as, ws(body), p.pc withBinding (id -> value), p.phi, p.xs, qeb.flatMapIns(ebF))

        Some(decomp(List(np), simpleWrap(Let(id, value, _)), s"Focus on let-body")(p))

      case _ => None
    }
  }
}
