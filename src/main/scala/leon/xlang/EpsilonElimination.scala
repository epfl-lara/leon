/* Copyright 2009-2013 EPFL, Lausanne */

package leon.xlang

import leon.TransformationPhase
import leon.LeonContext
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._
import leon.xlang.Trees._

object EpsilonElimination extends TransformationPhase {

  val name = "Epsilon Elimination"
  val description = "Remove all epsilons from the program"

  def apply(ctx: LeonContext, pgm: Program): Program = {

    val allFuns = pgm.definedFunctions
    allFuns.foreach(fd => fd.body.map(body => {
      val newBody = searchAndReplaceDFS{
        case eps@Epsilon(pred) => {
          val freshName = FreshIdentifier("epsilon")
          val newFunDef = new FunDef(freshName, eps.getType, Seq())
          val epsilonVar = EpsilonVariable(eps.posIntInfo)
          val resultVar = ResultVariable().setType(eps.getType)
          val postcondition = replace(Map(epsilonVar -> resultVar), pred)
          newFunDef.postcondition = Some(postcondition)
          Some(LetDef(newFunDef, FunctionInvocation(newFunDef, Seq())))
        }
        case _ => None
      }(body)
      fd.body = Some(newBody)
    }))
    pgm
  }

}
