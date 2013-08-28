/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis

import synthesis.search._

case class SearchCostModel(cm: CostModel) extends AOCostModel[TaskRunRule, TaskTryRules, Solution] {
  def taskCost(t: AOTask[Solution]) = t match {
    case ttr: TaskRunRule =>
      cm.ruleAppCost(ttr.app)
    case trr: TaskTryRules =>
      cm.problemCost(trr.p)
  }

  def solutionCost(s: Solution) = cm.solutionCost(s)
}

