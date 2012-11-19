package leon
package synthesis

import purescala.Trees._
import purescala.TreeOps._

import aographs.AOCost

case class SolutionCost(s: Solution) extends AOCost {
  val value = {
    val chooses = collectChooses(s.toExpr)
    val chooseCost = chooses.foldLeft(0)((i, c) => i + (1000 * math.pow(2, c.vars.size).toInt + formulaSize(c.pred)))

    formulaSize(s.toExpr) + chooseCost
  }
}

case class ProblemCost(p: Problem) extends AOCost {
  val value = math.pow(2, p.xs.size).toInt + formulaSize(p.phi)
}
