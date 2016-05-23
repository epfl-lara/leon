/* Copyright 2009-2016 EPFL, Lausanne */

package leon.xlang

import leon.{UnitPhase, LeonContext}
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.ExprOps._
import leon.xlang.Expressions._

object EpsilonElimination extends UnitPhase[Program] {

  val name = "Epsilon Elimination"
  val description = "Remove all epsilons from the program"

  def apply(ctx: LeonContext, pgm: Program) = {

    for (fd <- pgm.definedFunctions) {
      fd.fullBody = preTransformWithBinders({
        case (eps@Epsilon(pred, tpe), binders) =>
          val freshName = FreshIdentifier("epsilon")
          val bSeq = binders.toSeq
          val freshParams = bSeq.map { _.freshen }
          val newFunDef = new FunDef(freshName, Nil, freshParams map (ValDef(_)), tpe)
          val epsilonVar = EpsilonVariable(eps.getPos, tpe)
          val resId = FreshIdentifier("res", tpe)
          val eMap: Map[Expr, Expr] = bSeq.zip(freshParams).map {
            case (from, to) => (Variable(from), Variable(to))
          }.toMap ++ Seq((epsilonVar, Variable(resId)))
          val postcondition = replace(eMap, pred)
          newFunDef.postcondition = Some(Lambda(Seq(ValDef(resId)), postcondition))
          newFunDef.addFlags(fd.flags)
          newFunDef.addFlag(Annotation("extern", Seq()))
          LetDef(Seq(newFunDef), FunctionInvocation(newFunDef.typed, bSeq map Variable))

        case (other, _) => other
      }, fd.paramIds.toSet)(fd.fullBody)
    }
  }

}
