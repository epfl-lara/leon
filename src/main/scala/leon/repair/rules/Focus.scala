/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package repair
package rules

import purescala.Path
import purescala.Expressions._
import purescala.Common._
import purescala.Types._
import purescala.ExprOps._
import purescala.Constructors._
import purescala.Extractors._

import utils.fixpoint
import evaluators._

import synthesis._
import Witnesses._
import graph.AndNode

case object Focus extends PreprocessingRule("Focus") {

  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    hctx.parentNode match {
      case Some(an: AndNode) if an.ri.rule == Focus =>
        // We proceed as usual
      case Some(_) =>
        return None;
      case _ =>
        
    }

    val qeb = p.qebFiltered

    val fd      = hctx.functionContext
    val program = hctx.program

    val evaluator = new DefaultEvaluator(hctx, program)

    // Check how an expression behaves on tests
    //  - returns Some(true) if for all tests e evaluates to true
    //  - returns Some(false) if for all tests e evaluates to false
    //  - returns None otherwise
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

    def existsFailing(e: Expr, env: Map[Identifier, Expr], evaluator: DeterministicEvaluator): Boolean = {
      qeb.invalids.exists { ex =>
        evaluator.eval(e, (p.as zip ex.ins).toMap ++ env).result match {
          case Some(BooleanLiteral(b)) => b
          case _ => true
        }
      }
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

    def testCondition(guide: IfExpr) = {
      val IfExpr(cond, thenn, elze) = guide
      val spec = letTuple(p.xs, IfExpr(Not(cond), thenn, elze), p.phi)
      forAllTests(spec, Map(), new AngelicEvaluator(new RepairNDEvaluator(hctx, program, cond)))
    }

    guides.flatMap {
      case g @ IfExpr(c, thn, els) =>
        testCondition(g) match {
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

                Some(decomp(List(np), termWrap(IfExpr(c, _, els), c), s"Focus on if-then")(p))
              case Some(false) =>
                val np = Problem(p.as, ws(els), p.pc withCond not(c), p.phi, p.xs, qeb.filterIns(not(c)))

                Some(decomp(List(np), termWrap(IfExpr(c, thn, _), not(c)), s"Focus on if-else")(p))
              case None =>
                // We split
                val sub1 = p.copy(ws = ws(thn), pc = p.pc map (replace(Map(g -> thn), _)) withCond     c , eb = qeb.filterIns(c))
                val sub2 = p.copy(ws = ws(els), pc = p.pc map (replace(Map(g -> thn), _)) withCond Not(c), eb = qeb.filterIns(Not(c)))

                val onSuccess: List[Solution] => Option[Solution] = { 
                  case List(s1, s2) =>
                    Some(Solution(or(s1.pre, s2.pre), s1.defs++s2.defs, IfExpr(c, s1.term, s2.term)))
                  case _ =>
                    None
                }

                Some(decomp(List(sub1, sub2), onSuccess, s"Focus on both branches of '${c.asString}'"))
            }
        }

      case MatchExpr(scrut, cases) =>
        var pcSoFar = Path.empty

        // Generate subproblems for each match-case that fails at least one test.
        var casesInfos = for (c <- cases) yield {
          val map  = mapForPattern(scrut, c.pattern)

          val thisCond = matchCaseCondition(scrut, c)
          val prevPCSoFar = pcSoFar
          val cond = pcSoFar merge thisCond
          pcSoFar = pcSoFar merge thisCond.negate

          val subP = if (existsFailing(cond.toClause, map, evaluator)) {

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
              val subst = replaceFromIDs(substAs, (_:Expr))
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
              Some(Problem(newAs, newWs, newPc, newPhi, p.xs, newEb))
            } else {
              // Filter tests by the path-condition
              val eb2 = qeb.filterIns(cond.toClause)

              val newPc = cond withBindings vars.map(id => id -> map(id))

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

        if (existsFailing(elsePc.toClause, Map(), evaluator)) {
          val newCase    = MatchCase(WildcardPattern(None), None, NoTree(scrut.getType))

          val qeb2 = qeb.filterIns(elsePc.toClause)

          val newProblem = Problem(p.as, andJoin(wss), p.pc merge elsePc, p.phi, p.xs, qeb2)

          casesInfos :+= (newCase -> (Some(newProblem), elsePc))
        }

        // Is there at least one subproblem?
        if (casesInfos.exists(_._2._1.isDefined)) {
          val infosP = casesInfos.collect {
            case (c, (Some(p), pc)) => (c, (p, pc))
          }

          val nps = infosP.map(_._2._1).toList

          val appName = s"Focus on match-cases ${infosP.map(i => "'"+i._1.pattern.asString+"'").mkString(", ")}"

          val onSuccess: List[Solution] => Option[Solution] = { 
            case ss =>
              val matchSols = (infosP zip ss).map { case ((c, (pc)), s) => (c, (pc, s)) }

              val pres = matchSols.map {
                case (_, (pc, s)) =>
                  if(s.pre == BooleanLiteral(true)) {
                    BooleanLiteral(true)
                  } else {
                    p.pc and s.pre
                  }
              }

              val solsMap = matchSols.toMap

              val expr = MatchExpr(scrut, casesInfos.map { case (c, _) => solsMap.get(c) match {
                case Some((pc, s)) =>
                  c.copy(rhs = s.term)
                case None =>
                  c
              }})

              Some(Solution(orJoin(pres), ss.map(_.defs).reduceLeft(_ ++ _), expr))
          }

          Some(decomp(nps, onSuccess, appName)(p))
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

        Some(decomp(List(np), termWrap(Let(id, value, _)), s"Focus on let-body")(p))

      case _ => None
    }
  }
}
