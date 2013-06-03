/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package synthesis

import purescala.Trees._
import purescala.TreeOps._
import leon.xlang.Trees.LetDef

import synthesis.search.Cost

abstract class CostModel(val name: String) {
  def solutionCost(s: Solution): Cost
  def problemCost(p: Problem): Cost

  def ruleAppCost(app: RuleInstantiation): Cost = new Cost {
    val subSols = app.onSuccess.types.map {t => Solution.simplest(t) }.toList
    val simpleSol = app.onSuccess(subSols)

    val value = simpleSol match {
      case Some(sol) =>
        solutionCost(sol).value
      case None =>
        problemCost(app.problem).value
    }
  }
}

object CostModel {
  def default: CostModel = WeightedBranchesCostModel

  def all: Set[CostModel] = Set(
    NaiveCostModel,
    WeightedBranchesCostModel
  )
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

  def solutionCost(s: Solution): Cost = new Cost {
    val value = {
      val chooses = collectChooses(s.toExpr)
      val chooseCost = chooses.foldLeft(0)((i, c) => i + problemCost(Problem.fromChoose(c)).value)

      formulaSize(s.toExpr) + branchesCost(s.toExpr) + chooseCost
    }
  }

  def problemCost(p: Problem): Cost = new Cost {
    val value = p.xs.size
  }

}
