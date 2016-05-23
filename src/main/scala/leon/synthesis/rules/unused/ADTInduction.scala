/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules.unused

import purescala.Path
import purescala.Common._
import purescala.Expressions._
import purescala.Extractors._
import purescala.Constructors._
import purescala.ExprOps._
import purescala.Types._
import purescala.Definitions._

/** For every inductive variable, outputs a recursive solution if it exists */
case object ADTInduction extends Rule("ADT Induction") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    /* All input variables which are inductive in the post condition, along with their abstract data type. */
    val candidates = p.as.collect {
        case IsTyped(origId, act: AbstractClassType) if isInductiveOn(hctx.solverFactory)(p.pc, origId) => (origId, act)
    }

    val instances = for (candidate <- candidates) yield {
      val (origId, ct) = candidate
      // All input variables except the current inductive one.
      val oas = p.as.filterNot(_ == origId)

      // The return type (all output variables).
      val resType = tupleTypeWrap(p.xs.map(_.getType))

      // A new fresh variable similar to the current inductive one to perform induction.
      val inductOn     = FreshIdentifier(origId.name, origId.getType, true)

      // Duplicated arguments names based on existing remaining input variables.
      val residualArgs = oas.map(id => FreshIdentifier(id.name, id.getType, true))
      
      // Mapping from existing input variables to the new duplicated ones.
      val residualMap  = (oas zip residualArgs).map{ case (id, id2) => id -> Variable(id2) }.toMap
      
      // The value definition to be used in arguments of the recursive method.
      val residualArgDefs = residualArgs.map(ValDef(_))

      // Returns true if the case class has a field of type the one of the induction variable 
      // E.g. for `List` it returns true since `Cons(a: T, q: List[T])` and Cons is a List[T]
      def isAlternativeRecursive(ct: CaseClassType): Boolean = {
        ct.fields.exists(_.getType == origId.getType)
      }

      // True if one of the case classes has a field with the type being the one of the induction variable
      val isRecursive = ct.knownCCDescendants.exists(isAlternativeRecursive)

      // Map for getting a formula in the context of within the recursive function
      val substMap = residualMap + (origId -> Variable(inductOn))

      if (isRecursive) {

        // Transformation of conditions, variables and axioms to use the inner variables of the inductive function.
        val innerPhi = substAll(substMap, p.phi)
        val innerPC  = p.pc map (substAll(substMap, _))
        val innerWS  = substAll(substMap, p.ws)

        val subProblemsInfo = for (cct <- ct.knownCCDescendants) yield {
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
          val subPC  = innerPC map (substAll(Map(inductOn -> CaseClass(cct, newIds.map(Variable))), _))
          val subWS  = substAll(Map(inductOn -> CaseClass(cct, newIds.map(Variable))), innerWS)

          val subPre = IsInstanceOf(Variable(origId), cct)

          val subProblem = Problem(inputs ::: residualArgs, subWS, subPC withConds postFs, subPhi, p.xs)

          (subProblem, subPre, cct, newIds, recCalls)
        }

        val onSuccess: List[Solution] => Option[Solution] = {
          case sols =>
            var globalPre = List[Expr]()

            // The recursive inner function
            val newFun = new FunDef(FreshIdentifier("rec", alwaysShowUniqueID = true), Nil, ValDef(inductOn) +: residualArgDefs, resType)

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
              val outerPre = orJoin(globalPre)
              val funPre = p.pc withCond outerPre map (substAll(substMap, _))
              val funPost = substAll(substMap, p.phi)
              val idPost = FreshIdentifier("res", resType)

              newFun.precondition = funPre
              newFun.postcondition = Some(Lambda(Seq(ValDef(idPost)), letTuple(p.xs.toSeq, Variable(idPost), funPost)))

              newFun.body = Some(matchExpr(Variable(inductOn), cases))

              Some(Solution(outerPre,
                            sols.flatMap(_.defs).toSet + newFun,
                            FunctionInvocation(newFun.typed, Variable(origId) :: oas.map(Variable)),
                            sols.forall(_.isTrusted)
                          ))
            }
        }

        Some(decomp(subProblemsInfo.map(_._1).toList, onSuccess, s"ADT Induction on '${origId.asString}'"))
      } else { // If none of the descendants of the type is recursive, then nothing can be done.
        None
      }
    }

    instances.flatten
  }
}
