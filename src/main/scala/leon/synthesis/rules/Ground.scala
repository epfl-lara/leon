package leon
package synthesis
package rules

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._

case object Ground extends Rule("Ground", 500) {
  def instantiateOn(sctx: SynthesisContext, p: Problem): Traversable[RuleInstantiation] = {
    if (p.as.isEmpty) {

      val tpe = TupleType(p.xs.map(_.getType))

      sctx.solver.solveSAT(p.phi) match {
        case (Some(true), model) =>
          val sol = Solution(BooleanLiteral(true), Set(), Tuple(p.xs.map(valuateWithModel(model))).setType(tpe))
          Some(RuleInstantiation.immediateSuccess(sol))
        case (Some(false), model) =>
          val sol = Solution(BooleanLiteral(false), Set(), Error(p.phi+" is UNSAT!").setType(tpe))
          Some(RuleInstantiation.immediateSuccess(sol))
        case _ =>
          None
      }
    } else {
      None
    }
  }
}

