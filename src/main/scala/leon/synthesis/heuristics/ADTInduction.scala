/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package heuristics

import solvers._
import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

case object ADTInduction extends Rule("ADT Induction") with Heuristic {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    val candidates = p.as.collect {
        case IsTyped(origId, act: AbstractClassType) if isInductiveOn(sctx.solverFactory)(p.pc, origId) => (origId, act)
    }

    val instances = for (candidate <- candidates) yield {
      val (origId, ct) = candidate
      val oas = p.as.filterNot(_ == origId)

      val resType = TupleType(p.xs.map(_.getType))

      val inductOn     = FreshIdentifier(origId.name, true).setType(origId.getType)
      val residualArgs = oas.map(id => FreshIdentifier(id.name, true).setType(id.getType))
      val residualMap  = (oas zip residualArgs).map{ case (id, id2) => id -> Variable(id2) }.toMap
      val residualArgDefs = residualArgs.map(a => VarDecl(a, a.getType))

      def isAlternativeRecursive(ct: CaseClassType): Boolean = {
        ct.fields.exists(_.tpe == origId.getType)
      }

      val isRecursive = ct.knownCCDescendents.exists(isAlternativeRecursive)

      // Map for getting a formula in the context of within the recursive function
      val substMap = residualMap + (origId -> Variable(inductOn))

      if (isRecursive) {

        val innerPhi = substAll(substMap, p.phi)
        val innerPC  = substAll(substMap, p.pc)

        val subProblemsInfo = for (cct <- ct.knownCCDescendents) yield {
          var recCalls = Map[List[Identifier], List[Expr]]()
          var postFs   = List[Expr]()

          val newIds = cct.fields.map(vd => FreshIdentifier(vd.id.name, true).setType(vd.tpe)).toList

          val inputs = (for (id <- newIds) yield {
            if (id.getType == origId.getType) {
              val postXs  = p.xs map (id => FreshIdentifier("r", true).setType(id.getType))
              val postXsMap = (p.xs zip postXs).toMap.mapValues(Variable(_))

              recCalls += postXs -> (Variable(id) +: residualArgs.map(id => Variable(id)))

              postFs ::= substAll(postXsMap + (inductOn -> Variable(id)), innerPhi)
              id :: postXs
            } else {
              List(id)
            }
          }).flatten

          val subPhi = substAll(Map(inductOn -> CaseClass(cct, newIds.map(Variable(_)))), innerPhi)
          val subPC  = substAll(Map(inductOn -> CaseClass(cct, newIds.map(Variable(_)))), innerPC)

          val subPre = CaseClassInstanceOf(cct, Variable(origId))

          val subProblem = Problem(inputs ::: residualArgs, And(subPC :: postFs), subPhi, p.xs)

          (subProblem, subPre, cct, newIds, recCalls)
        }

        val onSuccess: List[Solution] => Option[Solution] = {
          case sols =>
            var globalPre = List[Expr]()

            val newFun = new FunDef(FreshIdentifier("rec", true), Nil, resType, VarDecl(inductOn, inductOn.getType) +: residualArgDefs)

            val cases = for ((sol, (problem, pre, cct, ids, calls)) <- (sols zip subProblemsInfo)) yield {
              globalPre ::= And(pre, sol.pre)

              val caze = CaseClassPattern(None, cct, ids.map(id => WildcardPattern(Some(id))))
              SimpleCase(caze, calls.foldLeft(sol.term){ case (t, (binders, callargs)) => LetTuple(binders, FunctionInvocation(newFun.typed, callargs), t) })
            }

            // Might be overly picky with obviously true pre (a.is[Cons] OR a.is[Nil])
            if (false && sols.exists(_.pre != BooleanLiteral(true))) {
              // Required to avoid an impossible cases, which suffices to
              // allow invalid programs. This might be too strong though: we
              // might only have to enforce it on solutions of base cases.
              None
            } else {
              val funPre = substAll(substMap, And(p.pc, Or(globalPre)))
              val funPost = substAll(substMap, p.phi)
              val idPost = FreshIdentifier("res").setType(resType)
              val outerPre = Or(globalPre)

              newFun.precondition = Some(funPre)
              newFun.postcondition = Some((idPost, LetTuple(p.xs.toSeq, Variable(idPost), funPost)))

              newFun.body = Some(MatchExpr(Variable(inductOn), cases))

              Some(Solution(Or(globalPre), 
                            sols.flatMap(_.defs).toSet+newFun,
                            FunctionInvocation(newFun.typed, Variable(origId) :: oas.map(Variable(_)))
                          ))
            }
        }

        Some(HeuristicInstantiation(p, this, subProblemsInfo.map(_._1).toList, onSuccess, "ADT Induction on '"+origId+"'"))
      } else {
        None
      }
    }

    instances.flatten
  }
}
