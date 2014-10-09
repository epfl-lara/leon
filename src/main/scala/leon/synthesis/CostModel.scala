/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package synthesis

import purescala.Trees._
import purescala.TreeOps._

abstract class CostModel(val name: String) {
  type Cost = Int

  def solutionCost(s: Solution): Cost
  def problemCost(p: Problem): Cost

  def ruleAppCost(app: RuleInstantiation): Cost = {
    val subSols = app.onSuccess.types.map {t => Solution.simplest(t) }.toList
    val simpleSol = app.onSuccess(subSols)

    simpleSol match {
      case Some(sol) =>
        solutionCost(sol)
      case None =>
        problemCost(app.problem)
    }
  }
}

case class ScaledCostModel(cm: CostModel, scale: Int) extends CostModel(cm.name+"/"+scale) {
  def solutionCost(s: Solution): Cost = Math.max(cm.solutionCost(s)/scale, 1)
  def problemCost(p: Problem): Cost = Math.max(cm.problemCost(p)/scale, 1)
  override def ruleAppCost(app: RuleInstantiation): Cost = Math.max(cm.ruleAppCost(app)/scale, 1)
}

object CostModel {
  def default: CostModel = ScaledCostModel(WeightedBranchesCostModel, 5)

  def all: Set[CostModel] = Set(
    ScaledCostModel(NaiveCostModel, 5),
    ScaledCostModel(WeightedBranchesCostModel, 5)
  )
}

case object NaiveCostModel extends CostModel("Naive") {
  def solutionCost(s: Solution): Cost = {
    val chooses = collectChooses(s.toExpr)
    val chooseCost = chooses.foldLeft(0)((i, c) => i + problemCost(Problem.fromChoose(c)))

    (formulaSize(s.toExpr) + chooseCost)/5+1
  }

  def problemCost(p: Problem): Cost = {
    1
  }

}

case object WeightedBranchesCostModel extends CostModel("WeightedBranches") {

  def branchesCost(e: Expr): Int = {
    case class BC(cost: Int, nesting: Int)

    def pre(e: Expr, c: BC) = {
      (e, c.copy(nesting = c.nesting + 1))
    }

    def costOfBranches(alts: Int, nesting: Int) = {
      if (nesting > 10) {
        alts
      } else {
        (10-nesting)*alts
      }
    }

    def post(e: Expr, bc: BC) = e match {
      case ie : IfExpr =>
       (e, bc.copy(cost = bc.cost + costOfBranches(2, bc.nesting)))
      case ie : LetDef => 
       (e, bc.copy(cost = bc.cost + costOfBranches(2, bc.nesting)))
      case ie : MatchExpr => 
       (e, bc.copy(cost = bc.cost + costOfBranches(ie.cases.size, bc.nesting)))
      case _ => 
       (e, bc)
    }

    def combiner(cs: Seq[BC]) = {
      cs.foldLeft(BC(0,0))((bc1, bc2) => BC(bc1.cost + bc2.cost, 0))
    }

    val (_, bc) = genericTransform[BC](pre, post, combiner)(BC(0, 0))(e)

    bc.cost
  }

  def solutionCost(s: Solution): Cost = {
    val chooses = collectChooses(s.toExpr)
    val chooseCost = chooses.foldLeft(0)((i, c) => i + problemCost(Problem.fromChoose(c)))

    formulaSize(s.toExpr) + branchesCost(s.toExpr) + chooseCost
  }

  def problemCost(p: Problem): Cost = {
    p.xs.size
  }

}
