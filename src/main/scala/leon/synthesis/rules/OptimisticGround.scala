package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._

class OptimisticGround(synth: Synthesizer) extends Rule("Optimistic Ground", synth, 150) {
  def attemptToApplyOn(p: Problem): RuleResult = {
    if (!p.as.isEmpty && !p.xs.isEmpty) {
      val xss = p.xs.toSet
      val ass = p.as.toSet

      val tpe = TupleType(p.xs.map(_.getType))

      var i = 0;
      var maxTries = 3;

      var result: Option[RuleResult]   = None
      var predicates: Seq[Expr]        = Seq()

      while (result.isEmpty && i < maxTries) {
        val phi = And(p.phi +: predicates)
        //println("SOLVING " + phi + " ...")
        synth.solver.solveSAT(phi) match {
          case (Some(true), satModel) =>
            val satXsModel = satModel.filterKeys(xss) 

            val newPhi = valuateWithModelIn(phi, xss, satModel)

            //println("REFUTING " + Not(newPhi) + "...")
            synth.solver.solveSAT(Not(newPhi)) match {
              case (Some(true), invalidModel) =>
                // Found as such as the xs break, refine predicates
                predicates = valuateWithModelIn(phi, ass, invalidModel) +: predicates

              case (Some(false), _) =>
                result = Some(RuleFastSuccess(Solution(BooleanLiteral(true), Set(), Tuple(p.xs.map(valuateWithModel(satModel))).setType(tpe))))

              case _ =>
                result = Some(RuleFastInapplicable())
            }

          case (Some(false), _) =>
            if (predicates.isEmpty) {
              result = Some(RuleFastSuccess(Solution(BooleanLiteral(false), Set(), Error(p.phi+" is UNSAT!").setType(tpe))))
            } else {
              result = Some(RuleFastInapplicable())
            }
          case _ =>
            result = Some(RuleFastInapplicable())
        }

        i += 1 
      }

      result.getOrElse(RuleFastInapplicable())
    } else {
      RuleInapplicable
    }
  }
}
