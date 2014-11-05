/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.Constructors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

case object IntInduction extends Rule("Int Induction") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    p.as match {
      case List(IsTyped(origId, IntegerType)) =>
        val tpe = tupleTypeWrap(p.xs.map(_.getType))

        val inductOn = FreshIdentifier(origId.name, true).setType(origId.getType)

        val postXs  = p.xs map (id => FreshIdentifier("r", true).setType(id.getType))

        val postXsMap = (p.xs zip postXs).toMap.mapValues(Variable(_))

        val newPhi     = subst(origId -> Variable(inductOn), p.phi)
        val newPc      = subst(origId -> Variable(inductOn), p.pc)
        val newWs      = subst(origId -> Variable(inductOn), p.ws)
        val postCondGT = substAll(postXsMap + (origId -> Minus(Variable(inductOn), InfiniteIntegerLiteral(1))), p.phi)
        val postCondLT = substAll(postXsMap + (origId -> Plus(Variable(inductOn), InfiniteIntegerLiteral(1))), p.phi)

        val subBase = Problem(List(), subst(origId -> InfiniteIntegerLiteral(0), p.ws), subst(origId -> InfiniteIntegerLiteral(0), p.pc), subst(origId -> InfiniteIntegerLiteral(0), p.phi), p.xs)
        val subGT   = Problem(inductOn :: postXs, newWs, and(GreaterThan(Variable(inductOn), InfiniteIntegerLiteral(0)), postCondGT, newPc), newPhi, p.xs)
        val subLT   = Problem(inductOn :: postXs, newWs, and(LessThan(Variable(inductOn), InfiniteIntegerLiteral(0)), postCondLT, newPc), newPhi, p.xs)

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

              val newFun = new FunDef(FreshIdentifier("rec", true), Nil, tpe, Seq(ValDef(inductOn, inductOn.getType)),DefType.MethodDef)
              val idPost = FreshIdentifier("res").setType(tpe)

              newFun.precondition = Some(preIn)
              newFun.postcondition = Some((idPost, letTuple(p.xs.toSeq, Variable(idPost), p.phi)))

              newFun.body = Some(
                IfExpr(Equals(Variable(inductOn), InfiniteIntegerLiteral(0)),
                  base.toExpr,
                IfExpr(GreaterThan(Variable(inductOn), InfiniteIntegerLiteral(0)),
                  letTuple(postXs, FunctionInvocation(newFun.typed, Seq(Minus(Variable(inductOn), InfiniteIntegerLiteral(1)))), gt.toExpr)
                , letTuple(postXs, FunctionInvocation(newFun.typed, Seq(Plus(Variable(inductOn), InfiniteIntegerLiteral(1)))), lt.toExpr)))
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
