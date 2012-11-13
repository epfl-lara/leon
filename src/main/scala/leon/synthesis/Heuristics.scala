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
    new OptimisticInjection(_)
  )
}

trait Heuristic {
  this: Rule =>

  override def toString = "H: "+name
}


class IntInduction(synth: Synthesizer) extends Rule("Int Induction", synth, 80) with Heuristic {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    p.as match {
      case List(origId) if origId.getType == Int32Type =>
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
            val newFun = new FunDef(FreshIdentifier("rec", true), tpe, Seq(VarDecl(inductOn, inductOn.getType)))
            newFun.body = Some(
              IfExpr(Equals(Variable(inductOn), IntLiteral(0)),
                base.toExpr,
              IfExpr(GreaterThan(Variable(inductOn), IntLiteral(0)),
                LetTuple(postXs, FunctionInvocation(newFun, Seq(Minus(Variable(inductOn), IntLiteral(1)))), gt.toExpr)
              , LetTuple(postXs, FunctionInvocation(newFun, Seq(Plus(Variable(inductOn), IntLiteral(1)))), lt.toExpr)))
            )

            Solution(BooleanLiteral(true), LetDef(newFun, FunctionInvocation(newFun, Seq(Variable(origId)))))
          case _ =>
            Solution.none
        }

        RuleStep(List(subBase, subGT, subLT), onSuccess)
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

      RuleStep(List(sub), forward)
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

      RuleStep(List(sub), forward)
    } else {
      RuleInapplicable
    }
  }
}

