package leon
package synthesis

import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

object Heuristics {
  def all = Set[Synthesizer => Rule](
    new IntInduction(_),
    new OptimisticInjection(_),
    new ADTInduction(_)
  )
}

trait Heuristic {
  this: Rule =>

  override def toString = "H: "+name

}

object HeuristicStep {
  def verifyPre(synth: Synthesizer, problem: Problem)(s: Solution): (Solution, Boolean) = {
    synth.solver.solveSAT(And(Not(s.pre), problem.phi)) match {
      case (Some(true), model) =>
        synth.reporter.warning("Heuristic failed to produce weakest precondition:")
        synth.reporter.warning(" - problem: "+problem)
        synth.reporter.warning(" - precondition: "+s.pre)
        (s, false)
      case _ =>
        (s, true)
    }
  }

  def apply(synth: Synthesizer, problem: Problem, subProblems: List[Problem], onSuccess: List[Solution] => Solution) = {
    RuleMultiSteps(subProblems, Nil, onSuccess.andThen(verifyPre(synth, problem)))
  }
}


class IntInduction(synth: Synthesizer) extends Rule("Int Induction", synth, 80) with Heuristic {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    p.as match {
      case List(IsTyped(origId, Int32Type)) =>
        val tpe = TupleType(p.xs.map(_.getType))

        val inductOn = FreshIdentifier(origId.name, true).setType(origId.getType)

        val postXs  = p.xs map (id => FreshIdentifier("r", true).setType(id.getType))

        val postXsMap = (p.xs zip postXs).toMap.mapValues(Variable(_))

        val newPhi     = subst(origId -> Variable(inductOn), p.phi)
        val postCondGT = substAll(postXsMap + (origId -> Minus(Variable(inductOn), IntLiteral(1))), p.phi)
        val postCondLT = substAll(postXsMap + (origId -> Plus(Variable(inductOn), IntLiteral(1))), p.phi)

        val subBase = Problem(List(), p.c, subst(origId -> IntLiteral(0), p.phi), p.xs)
        val subGT   = Problem(inductOn :: postXs, p.c, And(Seq(newPhi, GreaterThan(Variable(inductOn), IntLiteral(0)), postCondGT)), p.xs)
        val subLT   = Problem(inductOn :: postXs, p.c, And(Seq(newPhi, LessThan(Variable(inductOn), IntLiteral(0)), postCondLT)), p.xs)

        val onSuccess: List[Solution] => Solution = {
          case List(base, gt, lt) =>
            val preIn = Or(Seq(And(Equals(Variable(inductOn), IntLiteral(0)),      base.pre),
                               And(GreaterThan(Variable(inductOn), IntLiteral(0)), gt.pre),
                               And(LessThan(Variable(inductOn), IntLiteral(0)),    lt.pre)))
            val preOut = subst(inductOn -> Variable(origId), preIn)

            val newFun = new FunDef(FreshIdentifier("rec", true), tpe, Seq(VarDecl(inductOn, inductOn.getType)))
            newFun.precondition = Some(preIn)
            newFun.postcondition = Some(And(Equals(ResultVariable(), Tuple(p.xs.map(Variable(_)))), p.phi))

            newFun.body = Some(
              IfExpr(Equals(Variable(inductOn), IntLiteral(0)),
                base.toExpr,
              IfExpr(GreaterThan(Variable(inductOn), IntLiteral(0)),
                LetTuple(postXs, FunctionInvocation(newFun, Seq(Minus(Variable(inductOn), IntLiteral(1)))), gt.toExpr)
              , LetTuple(postXs, FunctionInvocation(newFun, Seq(Plus(Variable(inductOn), IntLiteral(1)))), lt.toExpr)))
            )


            Solution(preOut, base.defs++gt.defs++lt.defs+newFun, FunctionInvocation(newFun, Seq(Variable(origId))))
          case _ =>
            Solution.none
        }

        HeuristicStep(synth, p, List(subBase, subGT, subLT), onSuccess)
      case _ =>
        RuleInapplicable
    }
  }
}

class OptimisticInjection(synth: Synthesizer) extends Rule("Opt. Injection", synth, 50) with Heuristic {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    val TopLevelAnds(exprs) = p.phi

    val eqfuncalls = exprs.collect{
      case eq @ Equals(FunctionInvocation(fd, args), e) =>
        ((fd, e), args, eq : Expr)
      case eq @ Equals(e, FunctionInvocation(fd, args)) =>
        ((fd, e), args, eq : Expr)
    }

    val candidates = eqfuncalls.groupBy(_._1).filter(_._2.size > 1)
    if (!candidates.isEmpty) {

      var newExprs = exprs
      for (cands <- candidates.values) {
        val cand = cands.take(2)
        val toRemove = cand.map(_._3).toSet
        val argss    = cand.map(_._2)
        val args     = argss(0) zip argss(1)

        newExprs ++= args.map{ case (l, r) => Equals(l, r) }
        newExprs = newExprs.filterNot(toRemove)
      }

      val sub = p.copy(phi = And(newExprs))

      HeuristicStep(synth, p, List(sub), forward)
    } else {
      RuleInapplicable
    }
  }
}

class SelectiveInlining(synth: Synthesizer) extends Rule("Sel. Inlining", synth, 20) with Heuristic {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    val TopLevelAnds(exprs) = p.phi

    val eqfuncalls = exprs.collect{
      case eq @ Equals(FunctionInvocation(fd, args), e) =>
        ((fd, e), args, eq : Expr)
      case eq @ Equals(e, FunctionInvocation(fd, args)) =>
        ((fd, e), args, eq : Expr)
    }

    val candidates = eqfuncalls.groupBy(_._1).filter(_._2.size > 1)
    if (!candidates.isEmpty) {

      var newExprs = exprs
      for (cands <- candidates.values) {
        val cand = cands.take(2)
        val toRemove = cand.map(_._3).toSet
        val argss    = cand.map(_._2)
        val args     = argss(0) zip argss(1)

        newExprs ++= args.map{ case (l, r) => Equals(l, r) }
        newExprs = newExprs.filterNot(toRemove)
      }

      val sub = p.copy(phi = And(newExprs))

      HeuristicStep(synth, p, List(sub), forward)
    } else {
      RuleInapplicable
    }
  }
}

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

                postFs ::= substAll(postXsMap + (origId -> Variable(id)), innerPhi)
                id :: postXs
              } else {
                List(id)
              }
            }).flatten

            val subPhi = substAll(Map(inductOn -> CaseClass(ccd, newIds.map(Variable(_)))), innerPhi)

            val subPre = CaseClassInstanceOf(ccd, Variable(origId))

            val subProblem = Problem(inputs ::: residualArgs, And(p.c :: postFs), subPhi, p.xs)

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

            newFun.body = Some(MatchExpr(Variable(inductOn), cases))

            Solution(Or(globalPre), sols.flatMap(_.defs).toSet+newFun, FunctionInvocation(newFun, p.as.map(Variable(_))))
        }

        HeuristicStep(synth, p, subProblemsInfo.map(_._1).toList, onSuccess)
      } else {
        RuleInapplicable
      }
    } else {
      RuleInapplicable
    }
  }
}
