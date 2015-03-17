/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import solvers._
import purescala.Common._
import purescala.Expressions._
import purescala.Extractors._
import purescala.Constructors._
import purescala.ExprOps._
import purescala.Types._
import purescala.Definitions._

case object ADTLongInduction extends Rule("ADT Long Induction") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    val candidates = p.as.collect {
        case IsTyped(origId, act @ AbstractClassType(cd, tpe)) if isInductiveOn(hctx.sctx.solverFactory)(p.pc, origId) => (origId, act)
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
        case class InductCase(ids: List[Identifier],
                              calls: List[Identifier],
                              pattern: Pattern,
                              outerPC: Expr,
                              trMap: Map[Identifier, Expr])

        val init = InductCase(inductOn :: residualArgs, List(), WildcardPattern(Some(inductOn)), BooleanLiteral(true), Map(inductOn -> Variable(inductOn)))

        def isRec(id: Identifier) = id.getType == origId.getType

        def unrollPattern(id: Identifier, cct: CaseClassType, withIds: List[Identifier])(on: Pattern): Pattern = on match {
          case WildcardPattern(Some(pid)) if pid == id =>
            CaseClassPattern(None, cct, withIds.map(id => WildcardPattern(Some(id))))

          case CaseClassPattern(binder, sccd, sub) =>
            CaseClassPattern(binder, sccd, sub.map(unrollPattern(id, cct, withIds)))
            
          case _ => on
        }

        def unroll(ic: InductCase): List[InductCase] = {
          if (ic.ids.exists(isRec)) {
            val InductCase(ids, calls, pat, pc, trMap) = ic

            (for (id <- ids if isRec(id)) yield {
              for (cct <- ct.knownCCDescendents) yield {
                val subIds = cct.fields.map(vd => FreshIdentifier(vd.id.name, vd.getType, true)).toList

                val newIds = ids.filterNot(_ == id) ++ subIds
                val newCalls = if (subIds.nonEmpty) {
                  List(subIds.find(isRec)).flatten
                } else {
                  List()
                }

                //println(ccd)
                //println(subIds)
                val newPattern = unrollPattern(id, cct, subIds)(pat)

                val newMap = trMap.mapValues(v => substAll(Map(id -> CaseClass(cct, subIds.map(Variable))), v))

                InductCase(newIds, newCalls, newPattern, and(pc, CaseClassInstanceOf(cct, Variable(id))), newMap)
              }
            }).flatten
          } else {
            List(ic)
          }
        }

        val cases = unroll(init).flatMap(unroll)

        val innerPhi = substAll(substMap, p.phi)
        val innerPC  = substAll(substMap, p.pc)
        val innerWS  = substAll(substMap, p.ws)

        val subProblemsInfo = for (c <- cases) yield {
          val InductCase(ids, calls, pat, pc, trMap) = c

          // generate subProblem

          var recCalls = Map[List[Identifier], List[Expr]]()

          val subPC = substAll(trMap, innerPC)
          val subWS = substAll(trMap, innerWS)
          val subPhi = substAll(trMap, innerPhi)

          var postXss = List[Identifier]()
          var postFs = List[Expr]()

          for (cid <- calls) {
            val postXs  = p.xs map (id => FreshIdentifier("r", id.getType, true))
            postXss = postXss ::: postXs
            val postXsMap = (p.xs zip postXs).toMap.mapValues(Variable)
            postFs = substAll(postXsMap + (inductOn -> Variable(cid)), innerPhi) :: postFs

            recCalls += postXs -> (Variable(cid) +: residualArgs.map(id => Variable(id)))
          }

          val subProblem = Problem(c.ids ::: postXss, subWS, andJoin(subPC :: postFs), subPhi, p.xs)
          //println(subProblem)
          //println(recCalls)
          (subProblem, pat, recCalls, pc)
        }

        val onSuccess: List[Solution] => Option[Solution] = {
          case sols =>
            var globalPre = List[Expr]()

            val newFun = new FunDef(FreshIdentifier("rec", alwaysShowUniqueID = true), Nil, resType, ValDef(inductOn) +: residualArgDefs, DefType.MethodDef)

            val cases = for ((sol, (problem, pat, calls, pc)) <- sols zip subProblemsInfo) yield {
              globalPre ::= and(pc, sol.pre)

              SimpleCase(pat, calls.foldLeft(sol.term){ case (t, (binders, callargs)) => letTuple(binders, FunctionInvocation(newFun.typed, callargs), t) })
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

        Some(decomp(subProblemsInfo.map(_._1).toList, onSuccess, s"ADT Long Induction on '$origId'"))
      } else {
        None
      }
    }

    instances.flatten
  }
}
