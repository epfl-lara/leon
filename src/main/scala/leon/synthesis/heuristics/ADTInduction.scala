package leon
package synthesis
package heuristics

import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

class ADTInduction(synth: Synthesizer) extends Rule("ADT Induction", synth, 80) with Heuristic {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    val candidates = p.as.collect {
        case IsTyped(origId, AbstractClassType(cd)) => (origId, cd)
    }

    if (!candidates.isEmpty) {
      val (origId, cd) = candidates.head
      val oas = p.as.filterNot(_ == origId)

      val resType = TupleType(p.xs.map(_.getType))

      val inductOn     = FreshIdentifier(origId.name, true).setType(origId.getType)
      val residualArgs = oas.map(id => FreshIdentifier(id.name, true).setType(id.getType))
      val residualMap  = (oas zip residualArgs).map{ case (id, id2) => id -> Variable(id2) }.toMap
      val residualArgDefs = residualArgs.map(a => VarDecl(a, a.getType))

      def isAlternativeRecursive(cd: CaseClassDef): Boolean = {
        cd.fieldsIds.exists(_.getType == origId.getType)
      }

      val isRecursive = cd.knownDescendents.exists {
        case ccd: CaseClassDef => isAlternativeRecursive(ccd)
        case _ => false
      }

      if (isRecursive) {
        val newFun = new FunDef(FreshIdentifier("rec", true), resType, VarDecl(inductOn, inductOn.getType) +: residualArgDefs)

        val innerPhi = substAll(residualMap + (origId -> Variable(inductOn)), p.phi)
        val innerPC  = substAll(residualMap + (origId -> Variable(inductOn)), p.c)

        val subProblemsInfo = for (dcd <- cd.knownDescendents) yield dcd match {
          case ccd : CaseClassDef =>
            var recCalls = Map[List[Identifier], Expr]()
            var postFs   = List[Expr]()

            val newIds = ccd.fieldsIds.map(id => FreshIdentifier(id.name, true).setType(id.getType)).toList

            val inputs = (for (id <- newIds) yield {
              if (id.getType == origId.getType) {
                val postXs  = p.xs map (id => FreshIdentifier("r", true).setType(id.getType))
                val postXsMap = (p.xs zip postXs).toMap.mapValues(Variable(_))

                recCalls += postXs -> FunctionInvocation(newFun, Variable(id) +: residualArgs.map(id => Variable(id)))

                postFs ::= substAll(postXsMap + (inductOn -> Variable(id)), innerPhi)
                id :: postXs
              } else {
                List(id)
              }
            }).flatten

            val subPhi = substAll(Map(inductOn -> CaseClass(ccd, newIds.map(Variable(_)))), innerPhi)
            val subPC  = substAll(Map(inductOn -> CaseClass(ccd, newIds.map(Variable(_)))), innerPC)

            val subPre = CaseClassInstanceOf(ccd, Variable(origId))

            val subProblem = Problem(inputs ::: residualArgs, And(subPC :: postFs), subPhi, p.xs)

            (subProblem, subPre, ccd, newIds, recCalls)
          case _ =>
            sys.error("Woops, non case-class as descendent")
        }

        val onSuccess: List[Solution] => Solution = {
          case sols =>
            var globalPre = List[Expr]()

            val cases = for ((sol, (problem, pre, ccd, ids, calls)) <- (sols zip subProblemsInfo)) yield {
              globalPre ::= And(pre, sol.pre)

              val caze = CaseClassPattern(None, ccd, ids.map(id => WildcardPattern(Some(id))))
              SimpleCase(caze, calls.foldLeft(sol.term){ case (t, (binders, call)) => LetTuple(binders, call, t) })
            }

            val funPre = subst(origId -> Variable(inductOn), Or(globalPre))
            val outerPre = Or(globalPre)

            newFun.precondition = Some(funPre)
            newFun.postcondition = Some(LetTuple(p.xs.toSeq, ResultVariable(), p.phi))

            newFun.body = Some(MatchExpr(Variable(inductOn), cases))

            Solution(Or(globalPre), sols.flatMap(_.defs).toSet+newFun, FunctionInvocation(newFun, p.as.map(Variable(_))))
        }

        HeuristicOneStep(synth, p, subProblemsInfo.map(_._1).toList, onSuccess)
      } else {
        RuleInapplicable
      }
    } else {
      RuleInapplicable
    }
  }
}
