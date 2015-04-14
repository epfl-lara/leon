/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Common._
import purescala.Expressions._
import purescala.Extractors._
import purescala.Constructors._
import purescala.ExprOps._
import purescala.Types._
import purescala.Definitions._

case object ADTInduction extends Rule("ADT Induction") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val candidates = p.as.collect {
        case IsTyped(origId, act: AbstractClassType) if isInductiveOn(hctx.sctx.solverFactory)(p.pc, origId) => (origId, act)
    }

    val instances = for (candidate <- candidates) yield {
      val (origId, ct) = candidate
      val oas = p.as.filterNot(_ == origId)

      val resType = tupleTypeWrap(p.xs.map(_.getType))

      val inductOn     = FreshIdentifier(origId.name, origId.getType, true)
      val residualArgs = oas.map(id => FreshIdentifier(id.name, id.getType, true))
      val residualMap  = (oas zip residualArgs).map{ case (id, id2) => id -> Variable(id2) }.toMap
      val residualArgDefs = residualArgs.map(ValDef(_))

      def isAlternativeRecursive(ct: CaseClassType): Boolean = {
        ct.fields.exists(_.getType == origId.getType)
      }

      val isRecursive = ct.knownCCDescendents.exists(isAlternativeRecursive)

      // Map for getting a formula in the context of within the recursive function
      val substMap = residualMap + (origId -> Variable(inductOn))

      if (isRecursive) {

        val innerPhi = substAll(substMap, p.phi)
        val innerPC  = substAll(substMap, p.pc)
        val innerWS  = substAll(substMap, p.ws)

        val subProblemsInfo = for (cct <- ct.knownCCDescendents) yield {
          var recCalls = Map[List[Identifier], List[Expr]]()
          var postFs   = List[Expr]()

          val newIds = cct.fields.map(vd => FreshIdentifier(vd.id.name, vd.getType, true)).toList

          val inputs = (for (id <- newIds) yield {
            if (id.getType == origId.getType) {
              val postXs  = p.xs map (id => FreshIdentifier("r", id.getType, true))
              val postXsMap = (p.xs zip postXs).toMap.mapValues(Variable)

              recCalls += postXs -> (Variable(id) +: residualArgs.map(id => Variable(id)))

              postFs ::= substAll(postXsMap + (inductOn -> Variable(id)), innerPhi)
              id :: postXs
            } else {
              List(id)
            }
          }).flatten

          val subPhi = substAll(Map(inductOn -> CaseClass(cct, newIds.map(Variable))), innerPhi)
          val subPC  = substAll(Map(inductOn -> CaseClass(cct, newIds.map(Variable))), innerPC)
          val subWS  = substAll(Map(inductOn -> CaseClass(cct, newIds.map(Variable))), innerWS)

          val subPre = CaseClassInstanceOf(cct, Variable(origId))

          val subProblem = Problem(inputs ::: residualArgs, subWS, andJoin(subPC :: postFs), subPhi, p.xs)

          (subProblem, subPre, cct, newIds, recCalls)
        }

        val onSuccess: List[Solution] => Option[Solution] = {
          case sols =>
            var globalPre = List[Expr]()

            val newFun = new FunDef(FreshIdentifier("rec", alwaysShowUniqueID = true), Nil, resType, ValDef(inductOn) +: residualArgDefs, DefType.MethodDef)

            val cases = for ((sol, (problem, pre, cct, ids, calls)) <- sols zip subProblemsInfo) yield {
              globalPre ::= and(pre, sol.pre)

              val caze = CaseClassPattern(None, cct, ids.map(id => WildcardPattern(Some(id))))
              SimpleCase(caze, calls.foldLeft(sol.term){ case (t, (binders, callargs)) => letTuple(binders, FunctionInvocation(newFun.typed, callargs), t) })
            }

            // Might be overly picky with obviously true pre (a.is[Cons] OR a.is[Nil])
            if (false && sols.exists(_.pre != BooleanLiteral(true))) {
              // Required to avoid an impossible cases, which suffices to
              // allow invalid programs. This might be too strong though: we
              // might only have to enforce it on solutions of base cases.
              None
            } else {
              val funPre = substAll(substMap, and(p.pc, orJoin(globalPre)))
              val funPost = substAll(substMap, p.phi)
              val idPost = FreshIdentifier("res", resType)
              val outerPre = orJoin(globalPre)

              newFun.precondition = Some(funPre)
              newFun.postcondition = Some(Lambda(Seq(ValDef(idPost)), letTuple(p.xs.toSeq, Variable(idPost), funPost)))

              newFun.body = Some(matchExpr(Variable(inductOn), cases))

              Some(Solution(orJoin(globalPre),
                            sols.flatMap(_.defs).toSet+newFun,
                            FunctionInvocation(newFun.typed, Variable(origId) :: oas.map(Variable)),
                            sols.forall(_.isTrusted)
                          ))
            }
        }

        Some(decomp(subProblemsInfo.map(_._1).toList, onSuccess, s"ADT Induction on '$origId'"))
      } else {
        None
      }
    }

    instances.flatten
  }
}
