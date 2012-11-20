package leon
package synthesis

import purescala.Trees._
import purescala.TreeOps._

import aographs.AOCost

case class SolutionCost(s: Solution) extends AOCost {
  val value = {
    val chooses = collectChooses(s.toExpr)
    val chooseCost = chooses.foldLeft(0)((i, c) => i + ProblemCost(Problem.fromChoose(c)).value)

    formulaSize(s.toExpr) + chooseCost
  }
}

case class ProblemCost(p: Problem) extends AOCost {
  val value = math.pow(2, p.xs.size).toInt + formulaSize(p.phi)*1000
}

case class RuleApplicationCost(rule: Rule, app: RuleApplication) extends AOCost {
  val subSols = (1 to app.subProblemsCount).map {i => Solution.simplest }.toList
  val simpleSol = app.onSuccess(subSols)

  val value = SolutionCost(simpleSol).value*1000 + 1000-rule.priority
}
