package leon

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

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
