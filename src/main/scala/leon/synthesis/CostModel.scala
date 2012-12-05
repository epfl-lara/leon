package leon
package synthesis

import purescala.Trees._
import purescala.TreeOps._

import synthesis.search.Cost

abstract class CostModel(val name: String) {
  def solutionCost(s: Solution): Cost
  def problemCost(p: Problem): Cost

  def ruleAppCost(r: Rule, app: RuleApplication): Cost = new Cost {
    val subSols = (1 to app.subProblemsCount).map {i => Solution.simplest }.toList
    val simpleSol = app.onSuccess(subSols)

    val value = solutionCost(simpleSol).value
  }
}

object CostModel {
  def all: Set[CostModel] = Set(NaiveCostModel)
}

case object NaiveCostModel extends CostModel("Naive") {
  def solutionCost(s: Solution): Cost = new Cost {
    val value = {
      val chooses = collectChooses(s.toExpr)
      val chooseCost = chooses.foldLeft(0)((i, c) => i + problemCost(Problem.fromChoose(c)).value)

      formulaSize(s.toExpr) + chooseCost
    }
  }

  def problemCost(p: Problem): Cost = new Cost {
    val value = p.xs.size
  }

}
