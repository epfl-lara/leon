/* Copyright 2009-2014 EPFL, Lausanne */

package leon.xlang

import leon.TransformationPhase
import leon.LeonContext
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.ExprOps._
import leon.xlang.Expressions._

object EpsilonElimination extends TransformationPhase {

  val name = "Epsilon Elimination"
  val description = "Remove all epsilons from the program"

  def apply(ctx: LeonContext, pgm: Program): Program = {

    val allFuns = pgm.definedFunctions
    for {
      fd <- allFuns
      body <- fd.body
    } {
      val newBody = postMap{
        case eps@Epsilon(pred, tpe) =>
          val freshName   = FreshIdentifier("epsilon")
          val newFunDef   = new FunDef(freshName, Nil, tpe, Seq(), DefType.MethodDef)
          val epsilonVar  = EpsilonVariable(eps.getPos, tpe)
          val resId       = FreshIdentifier("res", tpe)
          val postcondition = replace(Map(epsilonVar -> Variable(resId)), pred)
          newFunDef.postcondition = Some(Lambda(Seq(ValDef(resId)), postcondition))
          Some(LetDef(newFunDef, FunctionInvocation(newFunDef.typed, Seq())))

        case _ =>
          None
      }(body)
      fd.body = Some(newBody)
    }
    pgm
  }

}
