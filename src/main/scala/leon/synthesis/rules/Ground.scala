package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._

case object Ground extends Rule("Ground", 500) {
  def attemptToApplyOn(sctx: SynthesisContext, p: Problem): RuleResult = {
    if (p.as.isEmpty) {

      val tpe = TupleType(p.xs.map(_.getType))

      sctx.solver.solveSAT(p.phi) match {
        case (Some(true), model) =>
          RuleFastSuccess(Solution(BooleanLiteral(true), Set(), Tuple(p.xs.map(valuateWithModel(model))).setType(tpe)))
        case (Some(false), model) =>
          RuleFastSuccess(Solution(BooleanLiteral(false), Set(), Error(p.phi+" is UNSAT!").setType(tpe)))
        case _ =>
          RuleInapplicable
      }
    } else {
      RuleInapplicable
    }
  }
}

