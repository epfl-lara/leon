package leon
package synthesis
package heuristics

import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

class IntInduction(synth: Synthesizer) extends Rule("Int Induction", synth, 50) with Heuristic {
  def attemptToApplyOn(p: Problem): RuleResult = {
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
            newFun.postcondition = Some(LetTuple(p.xs.toSeq, ResultVariable(), p.phi))

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

        HeuristicFastStep(synth, p, List(subBase, subGT, subLT), onSuccess)
      case _ =>
        RuleInapplicable
    }
  }
}
