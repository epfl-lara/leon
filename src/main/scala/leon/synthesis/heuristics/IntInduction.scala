/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis
package heuristics

import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

case object IntInduction extends Rule("Int Induction") with Heuristic {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    p.as match {
      case List(IsTyped(origId, Int32Type)) =>
        val tpe = TupleType(p.xs.map(_.getType))

        val inductOn = FreshIdentifier(origId.name, true).setType(origId.getType)

        val postXs  = p.xs map (id => FreshIdentifier("r", true).setType(id.getType))

        val postXsMap = (p.xs zip postXs).toMap.mapValues(Variable(_))

        val newPhi     = subst(origId -> Variable(inductOn), p.phi)
        val postCondGT = substAll(postXsMap + (origId -> Minus(Variable(inductOn), IntLiteral(1))), p.phi)
        val postCondLT = substAll(postXsMap + (origId -> Plus(Variable(inductOn), IntLiteral(1))), p.phi)

        val subBase = Problem(List(), p.pc, subst(origId -> IntLiteral(0), p.phi), p.xs)
        val subGT   = Problem(inductOn :: postXs, And(Seq(GreaterThan(Variable(inductOn), IntLiteral(0)), postCondGT, p.pc)), newPhi, p.xs)
        val subLT   = Problem(inductOn :: postXs, And(Seq(LessThan(Variable(inductOn), IntLiteral(0)), postCondLT, p.pc)), newPhi, p.xs)

        val onSuccess: List[Solution] => Option[Solution] = {
          case List(base, gt, lt) =>
            if (base.pre != BooleanLiteral(true) || (gt.pre != BooleanLiteral(true) && lt.pre != BooleanLiteral(true))) {
              // Required to avoid an impossible base-case, which suffices to
              // allow invalid programs.
              None
            } else {
              val preIn = Or(Seq(And(Equals(Variable(inductOn), IntLiteral(0)),      base.pre),
                                 And(GreaterThan(Variable(inductOn), IntLiteral(0)), gt.pre),
                                 And(LessThan(Variable(inductOn), IntLiteral(0)),    lt.pre)))
              val preOut = subst(inductOn -> Variable(origId), preIn)

              val newFun = new FunDef(FreshIdentifier("rec", true), tpe, Seq(VarDecl(inductOn, inductOn.getType)))
              newFun.precondition = Some(preIn)
              newFun.postcondition = Some(LetTuple(p.xs.toSeq, ResultVariable().setType(tpe), p.phi))

              newFun.body = Some(
                IfExpr(Equals(Variable(inductOn), IntLiteral(0)),
                  base.toExpr,
                IfExpr(GreaterThan(Variable(inductOn), IntLiteral(0)),
                  LetTuple(postXs, FunctionInvocation(newFun, Seq(Minus(Variable(inductOn), IntLiteral(1)))), gt.toExpr)
                , LetTuple(postXs, FunctionInvocation(newFun, Seq(Plus(Variable(inductOn), IntLiteral(1)))), lt.toExpr)))
              )


              Some(Solution(preOut, base.defs++gt.defs++lt.defs+newFun, FunctionInvocation(newFun, Seq(Variable(origId)))))
            }
          case _ =>
            None
        }

        Some(HeuristicInstantiation(p, this, List(subBase, subGT, subLT), onSuccess, "Int Induction on '"+origId+"'"))
      case _ =>
        None
    }
  }
}
