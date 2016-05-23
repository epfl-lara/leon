/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules.unused

import purescala.Common.FreshIdentifier
import purescala.Constructors._
import purescala.Definitions.{FunDef, ValDef}
import purescala.Expressions._
import purescala.Extractors.IsTyped
import purescala.Types.IntegerType

case object IntInduction extends Rule("Int Induction") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    p.as match {
      case List(IsTyped(origId, IntegerType)) =>
        val tpe = tupleTypeWrap(p.xs.map(_.getType))

        val inductOn = FreshIdentifier(origId.name, origId.getType, true)

        val postXs  = p.xs map (id => FreshIdentifier("r", id.getType, true))

        val postXsMap = (p.xs zip postXs).toMap.mapValues(Variable)

        val newPhi     = subst(origId -> Variable(inductOn), p.phi)
        val newPc      = p.pc map (subst(origId -> Variable(inductOn), _))
        val newWs      = subst(origId -> Variable(inductOn), p.ws)
        val postCondGT = substAll(postXsMap + (origId -> Minus(Variable(inductOn), InfiniteIntegerLiteral(1))), p.phi)
        val postCondLT = substAll(postXsMap + (origId -> Plus(Variable(inductOn), InfiniteIntegerLiteral(1))), p.phi)

        val subBase = Problem(List(), subst(origId -> InfiniteIntegerLiteral(0), p.ws), p.pc map (subst(origId -> InfiniteIntegerLiteral(0), _)), subst(origId -> InfiniteIntegerLiteral(0), p.phi), p.xs)
        val subGT   = Problem(inductOn :: postXs, newWs, newPc withCond and(GreaterThan(Variable(inductOn), InfiniteIntegerLiteral(0)), postCondGT), newPhi, p.xs)
        val subLT   = Problem(inductOn :: postXs, newWs, newPc withCond and(LessThan(Variable(inductOn), InfiniteIntegerLiteral(0)), postCondLT), newPhi, p.xs)

        val onSuccess: List[Solution] => Option[Solution] = {
          case List(base, gt, lt) =>
            if (base.pre != BooleanLiteral(true) || (gt.pre != BooleanLiteral(true) && lt.pre != BooleanLiteral(true))) {
              // Required to avoid an impossible base-case, which suffices to
              // allow invalid programs.
              None
            } else {
              val preIn = or(and(Equals(Variable(inductOn), InfiniteIntegerLiteral(0)),      base.pre),
                             and(GreaterThan(Variable(inductOn), InfiniteIntegerLiteral(0)), gt.pre),
                             and(LessThan(Variable(inductOn), InfiniteIntegerLiteral(0)),    lt.pre))
              val preOut = subst(inductOn -> Variable(origId), preIn)

              val newFun = new FunDef(FreshIdentifier("rec", alwaysShowUniqueID = true), Nil, Seq(ValDef(inductOn)), tpe)
              val idPost = FreshIdentifier("res", tpe)

              newFun.precondition = Some(preIn)
              newFun.postcondition = Some(Lambda(Seq(ValDef(idPost)), letTuple(p.xs.toSeq, Variable(idPost), p.phi)))

              newFun.body = Some(
                IfExpr(Equals(Variable(inductOn), InfiniteIntegerLiteral(0)),
                  base.toExpr,
                IfExpr(GreaterThan(Variable(inductOn), InfiniteIntegerLiteral(0)),
                  letTuple(postXs, FunctionInvocation(newFun.typed, Seq(Minus(Variable(inductOn), InfiniteIntegerLiteral(1)))), gt.toExpr),
                  letTuple(postXs, FunctionInvocation(newFun.typed, Seq(Plus(Variable(inductOn), InfiniteIntegerLiteral(1)))), lt.toExpr)))
              )


              Some(Solution(preOut, base.defs++gt.defs++lt.defs+newFun, FunctionInvocation(newFun.typed, Seq(Variable(origId))),
                Seq(base, gt, lt).forall(_.isTrusted)))
            }
          case _ =>
            None
        }

        Some(decomp(List(subBase, subGT, subLT), onSuccess, s"Int Induction on '$origId'"))
      case _ =>
        None
    }
  }
}
