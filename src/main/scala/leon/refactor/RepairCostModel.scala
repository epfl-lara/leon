/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package refactor
import synthesis._

import purescala.Trees._
import purescala.TreeOps._

case class RepairCostModel(cm: CostModel) extends CostModel(cm.name) {
  override def ruleAppCost(app: RuleInstantiation): Cost = {
    app.rule match {
      case rules.GuidedDecomp => 0
      case rules.CEGLESS => 0
      case _ => cm.ruleAppCost(app)
    }
  }
  def solutionCost(s: Solution) = cm.solutionCost(s)
  def problemCost(p: Problem) = cm.problemCost(p)
}


