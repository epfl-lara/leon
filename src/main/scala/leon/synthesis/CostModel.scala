/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis

import graph._

import purescala.Expressions._
import purescala.ExprOps._

abstract class CostModel(val name: String) {
  def solution(s: Solution): Cost
  def problem(p: Problem): Cost
  def andNode(an: AndNode, subs: Option[Seq[Cost]]): Cost

  def impossible: Cost

  def isImpossible(c: Cost): Boolean = {
    c >= impossible
  }
}

case class Cost(minSize: Int) extends AnyVal with Ordered[Cost] {
  def compare(that: Cost): Int = {
    this.minSize-that.minSize
  }

  def asString: String = {
    f"$minSize%3d"
  }
}

object CostModels {
  def default: CostModel = WeightedBranchesCostModel

  def all: Set[CostModel] = Set(
    NaiveCostModel,
    WeightedBranchesCostModel
  )
}

class WrappedCostModel(cm: CostModel, name: String) extends CostModel(name) {

  def solution(s: Solution): Cost = cm.solution(s)

  def problem(p: Problem): Cost = cm.problem(p)

  def andNode(an: AndNode, subs: Option[Seq[Cost]]): Cost = cm.andNode(an, subs)

  def impossible = cm.impossible
}

class SizeBasedCostModel(name: String) extends CostModel(name) {
  def solution(s: Solution) = {
    Cost(formulaSize(s.toExpr)/10)
  }

  def problem(p: Problem) = {
    Cost(1)
  }

  def andNode(an: AndNode, subs: Option[Seq[Cost]]) = {

    subs match {
      case Some(subs) if subs.isEmpty =>
        impossible

      case osubs =>
        val app = an.ri

        val subSols = app.onSuccess.types.map {t => Solution.simplest(t) }.toList
        val selfCost = app.onSuccess(subSols) match {
          case Some(sol) =>
            solution(sol).minSize - subSols.size
          case None =>
            1
        }
        Cost(osubs.toList.flatten.foldLeft(selfCost)(_ + _.minSize))
    }   
  }

  def impossible = Cost(200)
}

case object NaiveCostModel extends SizeBasedCostModel("Naive")

case object WeightedBranchesCostModel extends SizeBasedCostModel("WeightedBranches") {

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

  override def solution(s: Solution) = {
    Cost(formulaSize(s.toExpr) + branchesCost(s.toExpr))
  }

}
